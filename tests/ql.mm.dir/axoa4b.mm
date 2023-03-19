include "axoa4.mm"
include "oa4ctob.mm"

theorem axoa4b
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d


  assert |- ( ( a ->1 d ) ^ ( a v ( b ^ ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) ) ) =< d

  proof
    wva
    wvb
    wvc
    wvd
    wva
    wvb
    wvc
    wvd
    axoa4
    oa4ctob
end
