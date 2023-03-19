include "wer.mm"
include "wrel.mm"
include "cdm.mm"
include "wceq.mm"
include "ccnv.mm"
include "ccom.mm"
include "cun.mm"
include "wss.mm"
include "df-er.mm"
include "simp1bi.mm"

theorem errel
  let cA: class A
  let cR: class R


  assert |- ( R Er A -> Rel R )

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
    simp1bi
end
