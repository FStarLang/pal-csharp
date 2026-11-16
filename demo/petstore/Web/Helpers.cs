using System.Globalization;
using Microsoft.AspNetCore.Mvc.ViewFeatures;

namespace PetStore.Web;

public static class Money
{
    public static string Format(int cents) => (cents / 100m).ToString("C", CultureInfo.GetCultureInfo("en-US"));
}

public static class Flash
{
    public static void Set(ITempDataDictionary temp, string message, string kind)
    {
        temp["Message"] = message;
        temp["Kind"] = kind;
    }
}
