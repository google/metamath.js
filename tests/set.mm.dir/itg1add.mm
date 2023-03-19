include "caddc.mm"
include "crn.mm"
include "cxp.mm"
include "cres.mm"
include "cr.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cvol.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt2.mm"
include "eqid.mm"
include "itg1addlem5.mm"

theorem itg1add
  let wph: wff ph
  let cF: class F
  let cG: class G
  let vi: setvar i
  let vj: setvar j
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w
  let cI: class I
  let vv: setvar v
  let vx: setvar x
  let cP: class P
  let vu: setvar u
  assume i1fadd.1: |- ( ph -> F e. dom S.1 )
  assume i1fadd.2: |- ( ph -> G e. dom S.1 )


  assert |- ( ph -> ( S.1 ` ( F oF + G ) ) = ( ( S.1 ` F ) + ( S.1 ` G ) ) )

  proof
    wph
    caddc
    cF
    crn
    cG
    crn
    cxp
    cres
    #
    vi
    vj
    cF
    cG
    vi
    vj
    cr
    cr
    vi
    cv
    #
    cc0
    wceq
    vj
    cv
    #
    cc0
    wceq
    wa
    cc0
    cF
    ccnv
    @1
    csn
    cima
    cG
    ccnv
    @2
    csn
    cima
    cin
    cvol
    cfv
    cif
    cmpt2
    #
    i1fadd.1
    i1fadd.2
    @3
    eqid
    @0
    eqid
    itg1addlem5
end
