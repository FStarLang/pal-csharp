using Microsoft.AspNetCore.Mvc;
using Microsoft.AspNetCore.Mvc.RazorPages;
using PetStore.Verified;
using PetStore.Web.Data;

namespace PetStore.Web.Pages;

public class CartModel(Catalog catalog, Ops ops) : PageModel
{
    public List<CartLine> Lines { get; private set; } = [];

    public void OnGet() => Lines = catalog.Cart(Customer.Id(HttpContext));

    public IActionResult OnPostSet(int product, int qty)
    {
        ops.SetCartQty(Customer.Id(HttpContext), product, qty);
        return RedirectToPage();
    }

    public IActionResult OnPostCheckout()
    {
        Receipt r = ops.PlaceOrder(Customer.Id(HttpContext));
        if (r.OrderId != 0)
        {
            Flash.Set(TempData, $"Order #{r.OrderId} placed. Your new friends are on their way!", "ok");
            return RedirectToPage("/Orders");
        }
        Flash.Set(TempData, "Order not placed: your cart is empty, or we don't have enough of something in it. " +
                            "Nothing was charged or reserved.", "error");
        return RedirectToPage();
    }
}
