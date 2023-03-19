include "cop.mm"
include "csts.mm"
include "co.mm"
include "cusgr.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "crab.mm"
include "wf1.mm"
include "wb.mm"
include "cbs.mm"
include "setsvtx.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "rabeqdv.mm"
include "f1eq3.mm"
include "syl.mm"
include "mpbird.mm"
include "setsiedg.mm"
include "dmeqd.mm"
include "eqidd.mm"
include "f1eq123d.mm"
include "cvv.mm"
include "ovex.mm"
include "eqid.mm"
include "isusgrs.mm"
include "mp1i.mm"

theorem usgrstrrepe
  let wph: wff ph
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  assume usgrstrrepe.v: |- V = ( Base ` G )
  assume usgrstrrepe.i: |- I = ( .ef ` ndx )
  assume usgrstrrepe.s: |- ( ph -> G Struct X )
  assume usgrstrrepe.b: |- ( ph -> ( Base ` ndx ) e. dom G )
  assume usgrstrrepe.w: |- ( ph -> E e. W )
  assume usgrstrrepe.e: |- ( ph -> E : dom E -1-1-> { x e. ~P V | ( # ` x ) = 2 } )

  disjoint G x
  disjoint E x
  disjoint I x
  disjoint V x
  disjoint ph x
  assert |- ( ph -> ( G sSet <. I , E >. ) e. USGraph )

  proof
    wph
    cG
    cI
    cE
    cop
    #
    csts
    co
    #
    cusgr
    wcel
    #
    @1
    ciedg
    cfv
    #
    cdm
    #
    vx
    cv
    chash
    cfv
    c2
    wceq
    #
    vx
    @1
    cvtx
    cfv
    #
    cpw
    #
    crab
    #
    @3
    wf1
    #
    wph
    @9
    cE
    cdm
    #
    @8
    cE
    wf1
    #
    wph
    @11
    @10
    @5
    vx
    cV
    cpw
    #
    crab
    #
    cE
    wf1
    #
    usgrstrrepe.e
    wph
    @8
    @13
    wceq
    @11
    @14
    wb
    wph
    @5
    vx
    @7
    @12
    wph
    @6
    cV
    wph
    @6
    cG
    cbs
    cfv
    cV
    wph
    cE
    cG
    cI
    cW
    cX
    usgrstrrepe.i
    usgrstrrepe.s
    usgrstrrepe.b
    usgrstrrepe.w
    setsvtx
    usgrstrrepe.v
    syl6eqr
    pweqd
    rabeqdv
    @8
    @13
    @10
    cE
    f1eq3
    syl
    mpbird
    wph
    @4
    @10
    @8
    @8
    @3
    cE
    wph
    cE
    cG
    cI
    cW
    cX
    usgrstrrepe.i
    usgrstrrepe.s
    usgrstrrepe.b
    usgrstrrepe.w
    setsiedg
    #
    wph
    @3
    cE
    @15
    dmeqd
    wph
    @8
    eqidd
    f1eq123d
    mpbird
    @1
    cvv
    wcel
    @2
    @9
    wb
    wph
    cG
    @0
    csts
    ovex
    vx
    cvv
    @3
    @1
    @6
    @6
    eqid
    @3
    eqid
    isusgrs
    mp1i
    mpbird
end
