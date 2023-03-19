include "wcel.mm"
include "cnbgr.mm"
include "cvv.mm"
include "cv.mm"
include "cvtx.mm"
include "cfv.mm"
include "cpr.mm"
include "wss.mm"
include "cedg.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "cmpt2.mm"
include "wceq.mm"
include "co.mm"
include "df-nbgr.mm"
include "1vgrex.mm"
include "fveq2.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "biimpac.mm"
include "wa.mm"
include "fvex.mm"
include "difexi.mm"
include "rabexg.mm"
include "mp1i.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "sneq.mm"
include "adantl.mm"
include "difeq12d.mm"
include "wb.mm"
include "preq1.mm"
include "sseq1d.mm"
include "rexeqbidv.mm"
include "rabeqbidv.mm"
include "ovmpt2dv2.mm"
include "mpi.mm"

theorem nbgrval
  let ve: setvar e
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let vg: setvar g
  let vk: setvar k
  assume nbgrval.v: |- V = ( Vtx ` G )
  assume nbgrval.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint G e
  disjoint G n
  disjoint e n
  disjoint N e
  disjoint N n
  disjoint V e
  disjoint V n
  disjoint E g
  disjoint E k
  disjoint e g
  disjoint e k
  disjoint g k
  disjoint G g
  disjoint G k
  disjoint g n
  disjoint k n
  disjoint N g
  disjoint N k
  disjoint V g
  disjoint V k
  assert |- ( N e. V -> ( G NeighbVtx N ) = { n e. ( V \ { N } ) | E. e e. E { N , n } C_ e } )

  proof
    cN
    cV
    wcel
    #
    cnbgr
    vg
    vk
    cvv
    vg
    cv
    #
    cvtx
    cfv
    #
    vk
    cv
    #
    vn
    cv
    #
    cpr
    #
    ve
    cv
    #
    wss
    #
    ve
    @1
    cedg
    cfv
    #
    wrex
    #
    vn
    @2
    @3
    csn
    #
    cdif
    #
    crab
    #
    cmpt2
    wceq
    cG
    cN
    cnbgr
    co
    cN
    @4
    cpr
    #
    @6
    wss
    #
    ve
    cE
    wrex
    #
    vn
    cV
    cN
    csn
    #
    cdif
    #
    crab
    #
    wceq
    vk
    ve
    vg
    vn
    df-nbgr
    @0
    vg
    vk
    cG
    cN
    cvv
    @2
    @12
    @18
    cnbgr
    cvv
    cG
    cN
    cV
    nbgrval.v
    1vgrex
    @1
    cG
    wceq
    #
    @0
    cN
    @2
    wcel
    @19
    cV
    @2
    cN
    @19
    @2
    cG
    cvtx
    cfv
    #
    cV
    @1
    cG
    cvtx
    fveq2
    #
    nbgrval.v
    syl6reqr
    eleq2d
    biimpac
    @11
    cvv
    wcel
    @12
    cvv
    wcel
    @0
    @19
    @3
    cN
    wceq
    #
    wa
    #
    wa
    #
    @2
    @10
    @1
    cvtx
    fvex
    difexi
    @9
    vn
    @11
    cvv
    rabexg
    mp1i
    @24
    @9
    @15
    vn
    @11
    @17
    @23
    @11
    @17
    wceq
    @0
    @23
    @2
    cV
    @10
    @16
    @19
    @2
    cV
    wceq
    @22
    @19
    @2
    @20
    cV
    @21
    nbgrval.v
    syl6eqr
    adantr
    @22
    @10
    @16
    wceq
    @19
    @3
    cN
    sneq
    adantl
    difeq12d
    adantl
    @24
    @7
    @14
    ve
    @8
    cE
    @23
    @8
    cE
    wceq
    #
    @0
    @19
    @25
    @22
    @19
    @8
    cG
    cedg
    cfv
    cE
    @1
    cG
    cedg
    fveq2
    nbgrval.e
    syl6eqr
    adantr
    adantl
    @23
    @7
    @14
    wb
    #
    @0
    @22
    @26
    @19
    @22
    @5
    @13
    @6
    @3
    cN
    @4
    preq1
    sseq1d
    adantl
    adantl
    rexeqbidv
    rabeqbidv
    ovmpt2dv2
    mpi
end
