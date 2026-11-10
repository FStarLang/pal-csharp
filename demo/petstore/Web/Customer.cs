using System.Security.Cryptography;

namespace PetStore.Web;

/// <summary>
/// Who is shopping: a random positive id kept in a cookie. A demo stand-in for accounts;
/// the verified core treats the customer id as an arbitrary int.
/// </summary>
public static class Customer
{
    private const string Cookie = "petstore-customer";

    public static int Id(HttpContext http)
    {
        if (http.Items[Cookie] is int cached) return cached;
        if (!(http.Request.Cookies.TryGetValue(Cookie, out var raw) && int.TryParse(raw, out var id) && id > 0))
        {
            id = RandomNumberGenerator.GetInt32(1, int.MaxValue);
            http.Response.Cookies.Append(Cookie, id.ToString(),
                new CookieOptions { HttpOnly = true, IsEssential = true, MaxAge = TimeSpan.FromDays(30) });
        }
        http.Items[Cookie] = id;
        return id;
    }
}
