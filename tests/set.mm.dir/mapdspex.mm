include "csn.mm"
include "cfv.mm"
include "clsa.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "c0g.mm"
include "wa.mm"
include "clmod.mm"
include "lcdlmod.mm"
include "adantr.mm"
include "eqid.mm"
include "chlt.mm"
include "simpr.mm"
include "mapdat.mm"
include "islsati.mm"
include "syl2anc.mm"
include "lcd0vcl.mm"
include "fveq2.mm"
include "mapd0.mm"
include "lspsn0.mm"
include "syl.mm"
include "eqtr4d.mm"
include "sylan9eqr.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "dvhlmod.mm"
include "lsator0sp.mm"
include "mpjaodan.mm"

theorem mapdspex
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let vg: setvar g
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume mapdspex.h: |- H = ( LHyp ` K )
  assume mapdspex.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdspex.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdspex.v: |- V = ( Base ` U )
  assume mapdspex.n: |- N = ( LSpan ` U )
  assume mapdspex.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdspex.b: |- B = ( Base ` C )
  assume mapdspex.j: |- J = ( LSpan ` C )
  assume mapdspex.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdspex.x: |- ( ph -> X e. V )

  disjoint B g
  disjoint C g
  disjoint J g
  disjoint M g
  disjoint N g
  disjoint X g
  assert |- ( ph -> E. g e. B ( M ` ( N ` { X } ) ) = ( J ` { g } ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    cU
    clsa
    cfv
    #
    wcel
    #
    @0
    cM
    cfv
    #
    vg
    cv
    #
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    vg
    cB
    wrex
    #
    @0
    cU
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    wph
    @2
    wa
    #
    cC
    clmod
    wcel
    #
    @3
    cC
    clsa
    cfv
    #
    wcel
    @8
    wph
    @13
    @2
    wph
    cC
    cH
    cK
    cW
    mapdspex.h
    mapdspex.c
    mapdspex.k
    lcdlmod
    #
    adantr
    @12
    @1
    @14
    cC
    @0
    cU
    cH
    cK
    cM
    cW
    mapdspex.h
    mapdspex.m
    mapdspex.u
    @1
    eqid
    #
    mapdspex.c
    @14
    eqid
    #
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @2
    mapdspex.k
    adantr
    wph
    @2
    simpr
    mapdat
    vg
    @14
    @3
    cJ
    cB
    cC
    clmod
    mapdspex.b
    mapdspex.j
    @17
    islsati
    syl2anc
    wph
    @11
    wa
    cC
    c0g
    cfv
    #
    cB
    wcel
    #
    @3
    @18
    csn
    #
    cJ
    cfv
    #
    wceq
    #
    @8
    wph
    @19
    @11
    wph
    cC
    cH
    cK
    @18
    cB
    cW
    mapdspex.h
    mapdspex.c
    mapdspex.b
    @18
    eqid
    #
    mapdspex.k
    lcd0vcl
    adantr
    @11
    wph
    @3
    @10
    cM
    cfv
    #
    @21
    @0
    @10
    cM
    fveq2
    wph
    @24
    @20
    @21
    wph
    cC
    cU
    cH
    cK
    cM
    @9
    cW
    @18
    mapdspex.h
    mapdspex.m
    mapdspex.u
    @9
    eqid
    #
    mapdspex.c
    @23
    mapdspex.k
    mapd0
    wph
    @13
    @21
    @20
    wceq
    @15
    cJ
    cC
    @18
    @23
    mapdspex.j
    lspsn0
    syl
    eqtr4d
    sylan9eqr
    @7
    @22
    vg
    @18
    cB
    @4
    @18
    wceq
    #
    @6
    @21
    @3
    @26
    @5
    @20
    cJ
    @4
    @18
    sneq
    fveq2d
    eqeq2d
    rspcev
    syl2anc
    wph
    @1
    cN
    cV
    cU
    cX
    @9
    mapdspex.v
    mapdspex.n
    @25
    @16
    wph
    cU
    cH
    cK
    cW
    mapdspex.h
    mapdspex.u
    mapdspex.k
    dvhlmod
    mapdspex.x
    lsator0sp
    mpjaodan
end
