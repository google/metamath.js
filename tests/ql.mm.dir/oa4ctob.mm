include "wa.mm"
include "wi1.mm"
include "wo.mm"
include "oas.mm"

theorem oa4ctob
  let wva: term a
  let wvc: term c
  let wve: term e
  let wvg: term g
  assume oa4ctob.1: |- ( a ' ^ ( a v ( c ^ ( ( ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^ ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) ) =< g


  assert |- ( ( a ->1 g ) ^ ( a v ( c ^ ( ( ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^ ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) ) =< g

  proof
    wva
    wvc
    wva
    wvc
    wa
    wva
    wvg
    wi1
    #
    wvc
    wvg
    wi1
    #
    wa
    wo
    wva
    wve
    wa
    @0
    wve
    wvg
    wi1
    #
    wa
    wo
    wvc
    wve
    wa
    @1
    @2
    wa
    wo
    wa
    wo
    wa
    wvg
    oa4ctob.1
    oas
end
