include "wer.mm"
include "wrel.mm"
include "cdm.mm"
include "wceq.mm"
include "ccnv.mm"
include "ccom.mm"
include "cun.mm"
include "wss.mm"
include "df-er.mm"
include "simp2bi.mm"

theorem erdm
  let cA: class A
  let cR: class R


  assert |- ( R Er A -> dom R = A )

  proof
    cA
    cR
    wer
    cR
    wrel
    cR
    cdm
    cA
    wceq
    cR
    ccnv
    cR
    cR
    ccom
    cun
    cR
    wss
    cA
    cR
    df-er
    simp2bi
end
