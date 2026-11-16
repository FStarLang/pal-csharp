using Microsoft.AspNetCore.Mvc;
using Microsoft.AspNetCore.Mvc.RazorPages;
using PetStore.Verified;
using PetStore.Web.Data;

namespace PetStore.Web.Pages;

public class StaffModel(Catalog catalog, Ops ops) : PageModel
{
    public List<AuditRow> Audit { get; private set; } = [];
    public int OrderCount { get; private set; }

    public void OnGet()
    {
        Audit = catalog.Audit();
        OrderCount = catalog.Orders(null).Count;
    }

    public IActionResult OnPostRestock(int product, int n)
    {
        ops.Restock(product, n);
        Flash.Set(TempData, $"Delivery recorded.", "info");
        return RedirectToPage();
    }
}
