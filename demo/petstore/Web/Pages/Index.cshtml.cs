using Microsoft.AspNetCore.Mvc;
using Microsoft.AspNetCore.Mvc.RazorPages;
using PetStore.Verified;
using PetStore.Web.Data;

namespace PetStore.Web.Pages;

public class IndexModel(Catalog catalog, Ops ops) : PageModel
{
    public List<Product> Products { get; private set; } = [];

    public void OnGet() => Products = catalog.Products();

    public IActionResult OnPostAdd(int product, int qty)
    {
        int c = Customer.Id(HttpContext);
        int before = catalog.Cart(c).FirstOrDefault(l => l.Product.Id == product)?.Qty ?? 0;
        ops.AddToCart(c, product, qty);
        int after = catalog.Cart(c).FirstOrDefault(l => l.Product.Id == product)?.Qty ?? 0;
        if (after != before)
            Flash.Set(TempData, $"Added {qty} to your cart (now {after}).", "ok");
        else
            Flash.Set(TempData, $"Couldn't add that: carts hold at most {Model.MaxCartQty} of each pet.", "error");
        return RedirectToPage();
    }
}
