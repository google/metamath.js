include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "ccnv.mm"
include "wceq.mm"
include "cdif.mm"
include "wrex.mm"
include "cbs.mm"
include "wa.mm"
include "eqid.mm"
include "atbase.mm"
include "anim2i.mm"
include "wi.mm"
include "chlt.mm"
include "crn.mm"
include "adantr.mm"
include "eldifi.mm"
include "dihlsprn.mm"
include "syl2an.mm"
include "dihcnvcl.mm"
include "syl2anc.mm"
include "eleq1a.mm"
include "syl.mm"
include "rexlimdva.mm"
include "imdistani.mm"
include "simpr.mm"
include "dihatexv.mm"
include "dihcnvid2.mm"
include "eqeq2d.mm"
include "wb.mm"
include "simplr.mm"
include "dih11.mm"
include "syl3anc.mm"
include "bitr3d.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "pm5.21nd.mm"

theorem dihatexv2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume dihatexv2.a: |- A = ( Atoms ` K )
  assume dihatexv2.h: |- H = ( LHyp ` K )
  assume dihatexv2.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihatexv2.v: |- V = ( Base ` U )
  assume dihatexv2.o: |- .0. = ( 0g ` U )
  assume dihatexv2.n: |- N = ( LSpan ` U )
  assume dihatexv2.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihatexv2.k: |- ( ph -> ( K e. HL /\ W e. H ) )

  disjoint A x
  disjoint I x
  disjoint K x
  disjoint N x
  disjoint Q x
  disjoint V x
  disjoint W x
  disjoint ph x
  assert |- ( ph -> ( Q e. A <-> E. x e. ( V \ { .0. } ) Q = ( `' I ` ( N ` { x } ) ) ) )

  proof
    wph
    cQ
    cA
    wcel
    #
    cQ
    vx
    cv
    #
    csn
    cN
    cfv
    #
    cI
    ccnv
    cfv
    #
    wceq
    #
    vx
    cV
    c.0
    csn
    #
    cdif
    #
    wrex
    #
    wph
    cQ
    cK
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @0
    @9
    wph
    cA
    @8
    cQ
    cK
    @8
    eqid
    #
    dihatexv2.a
    atbase
    anim2i
    wph
    @7
    @9
    wph
    @4
    @9
    vx
    @6
    wph
    @1
    @6
    wcel
    #
    wa
    #
    @3
    @8
    wcel
    #
    @4
    @9
    wi
    @13
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @2
    cI
    crn
    wcel
    #
    @14
    wph
    @15
    @12
    dihatexv2.k
    adantr
    wph
    @15
    @1
    cV
    wcel
    #
    @16
    @12
    dihatexv2.k
    @1
    cV
    @5
    eldifi
    #
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    @1
    dihatexv2.h
    dihatexv2.u
    dihatexv2.v
    dihatexv2.n
    dihatexv2.i
    dihlsprn
    #
    syl2an
    @8
    cH
    cI
    cK
    cW
    @2
    @11
    dihatexv2.h
    dihatexv2.i
    dihcnvcl
    #
    syl2anc
    @3
    @8
    cQ
    eleq1a
    syl
    rexlimdva
    imdistani
    @10
    @0
    cQ
    cI
    cfv
    #
    @2
    wceq
    #
    vx
    @6
    wrex
    @7
    @10
    vx
    cA
    @8
    cQ
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    c.0
    @11
    dihatexv2.a
    dihatexv2.h
    dihatexv2.u
    dihatexv2.v
    dihatexv2.o
    dihatexv2.n
    dihatexv2.i
    wph
    @15
    @9
    dihatexv2.k
    adantr
    #
    wph
    @9
    simpr
    dihatexv
    @10
    @22
    @4
    vx
    @6
    @10
    @12
    wa
    #
    @21
    @3
    cI
    cfv
    #
    wceq
    #
    @22
    @4
    @24
    @25
    @2
    @21
    @24
    @15
    @16
    @25
    @2
    wceq
    @10
    @15
    @12
    @23
    adantr
    #
    @10
    @15
    @17
    @16
    @12
    @23
    @18
    @19
    syl2an
    #
    cH
    cI
    cK
    cW
    @2
    dihatexv2.h
    dihatexv2.i
    dihcnvid2
    syl2anc
    eqeq2d
    @24
    @15
    @9
    @14
    @26
    @4
    wb
    @27
    wph
    @9
    @12
    simplr
    @24
    @15
    @16
    @14
    @27
    @28
    @20
    syl2anc
    @8
    cH
    cI
    cK
    cW
    cQ
    @3
    @11
    dihatexv2.h
    dihatexv2.i
    dih11
    syl3anc
    bitr3d
    rexbidva
    bitrd
    pm5.21nd
end
