include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "cdgr.mm"
include "ccnv.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cn0.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "plyssc.mm"
include "sseli.mm"
include "cv.mm"
include "ccoe.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "supeq1d.mm"
include "df-dgr.mm"
include "cr.mm"
include "wss.mm"
include "wor.mm"
include "nn0ssre.mm"
include "ltso.mm"
include "soss.mm"
include "mp2.mm"
include "supex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem dgrval
  let cA: class A
  let cS: class S
  let cF: class F
  let va: setvar a
  let vf: setvar f
  let vn: setvar n
  let vx: setvar x
  let vk: setvar k
  let vz: setvar z
  assume dgrval.1: |- A = ( coeff ` F )


  assert |- ( F e. ( Poly ` S ) -> ( deg ` F ) = sup ( ( `' A " ( CC \ { 0 } ) ) , NN0 , < ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    cF
    cc
    cply
    cfv
    #
    wcel
    cF
    cdgr
    cfv
    cA
    ccnv
    #
    cc
    cc0
    csn
    cdif
    #
    cima
    #
    cn0
    clt
    csup
    #
    wceq
    @0
    @1
    cF
    cS
    plyssc
    sseli
    vf
    cF
    vf
    cv
    #
    ccoe
    cfv
    #
    ccnv
    #
    @3
    cima
    #
    cn0
    clt
    csup
    @5
    @1
    cdgr
    @6
    cF
    wceq
    #
    cn0
    @9
    @4
    clt
    @10
    @8
    @2
    @3
    @10
    @7
    cA
    @10
    @7
    cF
    ccoe
    cfv
    cA
    @6
    cF
    ccoe
    fveq2
    dgrval.1
    syl6eqr
    cnveqd
    imaeq1d
    supeq1d
    vf
    df-dgr
    cn0
    @4
    clt
    cn0
    cr
    wss
    cr
    clt
    wor
    cn0
    clt
    wor
    nn0ssre
    ltso
    cn0
    cr
    clt
    soss
    mp2
    supex
    fvmpt
    syl
end
