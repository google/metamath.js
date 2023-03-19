include "wfn.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wfrfun.mm"
include "cv.mm"
include "cpred.mm"
include "cres.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "eqid.mm"
include "wfrlem16.mm"
include "df-fn.mm"
include "mpbir2an.mm"

theorem wfr1
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let vz: setvar z
  assume wfr1.1: |- R We A
  assume wfr1.2: |- R Se A
  assume wfr1.3: |- F = wrecs ( R , A , G )


  assert |- F Fn A

  proof
    cF
    cA
    wfn
    cF
    wfun
    cF
    cdm
    cA
    wceq
    cA
    cR
    cF
    cG
    wfr1.1
    wfr1.2
    wfr1.3
    wfrfun
    vz
    cA
    cF
    vz
    cv
    #
    cF
    cA
    cR
    @0
    cpred
    cres
    cG
    cfv
    cop
    csn
    cun
    #
    cR
    cF
    cG
    wfr1.1
    wfr1.2
    wfr1.3
    @1
    eqid
    wfrlem16
    cF
    cA
    df-fn
    mpbir2an
end
