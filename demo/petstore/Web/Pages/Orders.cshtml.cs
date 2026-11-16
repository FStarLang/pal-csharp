using Microsoft.AspNetCore.Mvc.RazorPages;
using PetStore.Web.Data;

namespace PetStore.Web.Pages;

public class OrdersModel(Catalog catalog) : PageModel
{
    public List<Order> Orders { get; private set; } = [];

    public void OnGet() => Orders = catalog.Orders(Customer.Id(HttpContext));
}
