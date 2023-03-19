include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "wcel.mm"
include "wss.mm"
include "eqid.mm"
include "lcfls1c.mm"
include "simplbi.mm"
include "syl.mm"
include "lclkrlem2.mm"
include "cin.mm"
include "chlt.mm"
include "wa.mm"
include "cbs.mm"
include "dvhlmod.mm"
include "w3a.mm"
include "lcfls1lem.mm"
include "sylib.mm"
include "simp1d.mm"
include "ldualvaddcl.mm"
include "lkrssv.mm"
include "lkrin.mm"
include "dochss.mm"
include "syl3anc.mm"
include "clsm.mm"
include "cdjh.mm"
include "cdih.mm"
include "crn.mm"
include "simp2d.mm"
include "lcfl5a.mm"
include "mpbid.mm"
include "dochdmm1.mm"
include "dochcl.mm"
include "syl2anc.mm"
include "dochkrsm.mm"
include "dochlss.mm"
include "djhlsmcl.mm"
include "eqtr4d.mm"
include "simp3d.mm"
include "csubg.mm"
include "wb.mm"
include "clmod.mm"
include "lsssssubg.mm"
include "sseldd.mm"
include "lsmlub.mm"
include "mpbi2and.mm"
include "eqsstrd.mm"
include "sstrd.mm"
include "sylanbrc.mm"

theorem lclkrslem2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  assume lclkrslem1.h: |- H = ( LHyp ` K )
  assume lclkrslem1.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrslem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrslem1.s: |- S = ( LSubSp ` U )
  assume lclkrslem1.f: |- F = ( LFnl ` U )
  assume lclkrslem1.l: |- L = ( LKer ` U )
  assume lclkrslem1.d: |- D = ( LDual ` U )
  assume lclkrslem1.r: |- R = ( Scalar ` U )
  assume lclkrslem1.b: |- B = ( Base ` R )
  assume lclkrslem1.t: |- .x. = ( .s ` D )
  assume lclkrslem1.c: |- C = { f e. F | ( ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) /\ ( ._|_ ` ( L ` f ) ) C_ Q ) }
  assume lclkrslem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrslem1.q: |- ( ph -> Q e. S )
  assume lclkrslem1.g: |- ( ph -> G e. C )
  assume lclkrslem2.p: |- .+ = ( +g ` D )
  assume lclkrslem2.e: |- ( ph -> E e. C )

  disjoint ._|_ f
  disjoint F f
  disjoint G f
  disjoint L f
  disjoint Q f
  disjoint .x. f
  disjoint E f
  disjoint .+ f
  disjoint X f
  assert |- ( ph -> ( E .+ G ) e. C )

  proof
    wph
    cE
    cG
    c.pl
    co
    #
    vf
    cv
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @1
    wceq
    vf
    cF
    crab
    #
    wcel
    @0
    cL
    cfv
    #
    c.pe
    cfv
    #
    cQ
    wss
    @0
    cC
    wcel
    wph
    @2
    cD
    c.pl
    cU
    vf
    cE
    cF
    cG
    cH
    cK
    cL
    c.pe
    cW
    lclkrslem1.h
    lclkrslem1.o
    lclkrslem1.u
    lclkrslem1.f
    lclkrslem1.l
    lclkrslem1.d
    lclkrslem2.p
    @2
    eqid
    #
    lclkrslem1.k
    wph
    cE
    cC
    wcel
    #
    cE
    @2
    wcel
    #
    lclkrslem2.e
    @6
    @7
    cE
    cL
    cfv
    #
    c.pe
    cfv
    #
    cQ
    wss
    #
    cC
    @2
    cQ
    vf
    cF
    cE
    cL
    c.pe
    lclkrslem1.c
    @5
    lcfls1c
    simplbi
    syl
    wph
    cG
    cC
    wcel
    #
    cG
    @2
    wcel
    #
    lclkrslem1.g
    @11
    @12
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    cQ
    wss
    #
    cC
    @2
    cQ
    vf
    cF
    cG
    cL
    c.pe
    lclkrslem1.c
    @5
    lcfls1c
    simplbi
    syl
    lclkrlem2
    wph
    @4
    @8
    @13
    cin
    #
    c.pe
    cfv
    #
    cQ
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @3
    cU
    cbs
    cfv
    #
    wss
    @16
    @3
    wss
    @4
    @17
    wss
    lclkrslem1.k
    wph
    cF
    @0
    cL
    @19
    cU
    @19
    eqid
    #
    lclkrslem1.f
    lclkrslem1.l
    wph
    cU
    cH
    cK
    cW
    lclkrslem1.h
    lclkrslem1.u
    lclkrslem1.k
    dvhlmod
    #
    wph
    cD
    c.pl
    cF
    cE
    cG
    cU
    lclkrslem1.f
    lclkrslem1.d
    lclkrslem2.p
    @21
    wph
    cE
    cF
    wcel
    #
    @9
    c.pe
    cfv
    @8
    wceq
    #
    @10
    wph
    @6
    @22
    @23
    @10
    w3a
    lclkrslem2.e
    cC
    cQ
    vf
    cF
    cE
    cL
    c.pe
    lclkrslem1.c
    lcfls1lem
    sylib
    #
    simp1d
    #
    wph
    cG
    cF
    wcel
    #
    @14
    c.pe
    cfv
    @13
    wceq
    #
    @15
    wph
    @11
    @26
    @27
    @15
    w3a
    lclkrslem1.g
    cC
    cQ
    vf
    cF
    cG
    cL
    c.pe
    lclkrslem1.c
    lcfls1lem
    sylib
    #
    simp1d
    #
    ldualvaddcl
    lkrssv
    wph
    cD
    c.pl
    cF
    cE
    cG
    cL
    cU
    lclkrslem1.f
    lclkrslem1.l
    lclkrslem1.d
    lclkrslem2.p
    @21
    @25
    @29
    lkrin
    cU
    cH
    cK
    c.pe
    @19
    cW
    @16
    @3
    lclkrslem1.h
    lclkrslem1.u
    @20
    lclkrslem1.o
    dochss
    syl3anc
    wph
    @17
    @9
    @14
    cU
    clsm
    cfv
    #
    co
    #
    cQ
    wph
    @17
    @9
    @14
    cW
    cK
    cdjh
    cfv
    cfv
    #
    co
    #
    @31
    wph
    cU
    cH
    cW
    cK
    cdih
    cfv
    cfv
    #
    @32
    cK
    c.pe
    @19
    cW
    @8
    @13
    lclkrslem1.h
    @34
    eqid
    #
    lclkrslem1.u
    @20
    lclkrslem1.o
    @32
    eqid
    #
    lclkrslem1.k
    wph
    @23
    @8
    @34
    crn
    #
    wcel
    wph
    @22
    @23
    @10
    @24
    simp2d
    wph
    cU
    cF
    cE
    cH
    @34
    cK
    cL
    c.pe
    cW
    lclkrslem1.h
    @35
    lclkrslem1.o
    lclkrslem1.u
    lclkrslem1.f
    lclkrslem1.l
    lclkrslem1.k
    @25
    lcfl5a
    mpbid
    wph
    @27
    @13
    @37
    wcel
    wph
    @26
    @27
    @15
    @28
    simp2d
    wph
    cU
    cF
    cG
    cH
    @34
    cK
    cL
    c.pe
    cW
    lclkrslem1.h
    @35
    lclkrslem1.o
    lclkrslem1.u
    lclkrslem1.f
    lclkrslem1.l
    lclkrslem1.k
    @29
    lcfl5a
    mpbid
    dochdmm1
    wph
    @31
    @37
    wcel
    @31
    @33
    wceq
    wph
    @30
    cU
    cF
    cG
    cH
    @34
    cK
    cL
    c.pe
    cW
    @9
    lclkrslem1.h
    @35
    lclkrslem1.o
    lclkrslem1.u
    @30
    eqid
    #
    lclkrslem1.f
    lclkrslem1.l
    lclkrslem1.k
    wph
    @18
    @8
    @19
    wss
    #
    @9
    @37
    wcel
    lclkrslem1.k
    wph
    cF
    cE
    cL
    @19
    cU
    @20
    lclkrslem1.f
    lclkrslem1.l
    @21
    @25
    lkrssv
    #
    cU
    cH
    @34
    cK
    c.pe
    @19
    cW
    @8
    lclkrslem1.h
    @35
    lclkrslem1.u
    @20
    lclkrslem1.o
    dochcl
    syl2anc
    @29
    dochkrsm
    wph
    @30
    cS
    cU
    cH
    @34
    @32
    cK
    @19
    cW
    @9
    @14
    lclkrslem1.h
    lclkrslem1.u
    @20
    lclkrslem1.s
    @38
    @35
    @36
    lclkrslem1.k
    wph
    @18
    @39
    @9
    cS
    wcel
    lclkrslem1.k
    @40
    cS
    cU
    cH
    cK
    c.pe
    @19
    cW
    @8
    lclkrslem1.h
    lclkrslem1.u
    @20
    lclkrslem1.s
    lclkrslem1.o
    dochlss
    syl2anc
    #
    wph
    @18
    @13
    @19
    wss
    @14
    cS
    wcel
    lclkrslem1.k
    wph
    cF
    cG
    cL
    @19
    cU
    @20
    lclkrslem1.f
    lclkrslem1.l
    @21
    @29
    lkrssv
    cS
    cU
    cH
    cK
    c.pe
    @19
    cW
    @13
    lclkrslem1.h
    lclkrslem1.u
    @20
    lclkrslem1.s
    lclkrslem1.o
    dochlss
    syl2anc
    #
    djhlsmcl
    mpbid
    eqtr4d
    wph
    @10
    @15
    @31
    cQ
    wss
    #
    wph
    @22
    @23
    @10
    @24
    simp3d
    wph
    @26
    @27
    @15
    @28
    simp3d
    wph
    @9
    cU
    csubg
    cfv
    #
    wcel
    @14
    @44
    wcel
    cQ
    @44
    wcel
    @10
    @15
    wa
    @43
    wb
    wph
    cS
    @44
    @9
    wph
    cU
    clmod
    wcel
    cS
    @44
    wss
    @21
    cS
    cU
    lclkrslem1.s
    lsssssubg
    syl
    #
    @41
    sseldd
    wph
    cS
    @44
    @14
    @45
    @42
    sseldd
    wph
    cS
    @44
    cQ
    @45
    lclkrslem1.q
    sseldd
    @30
    @9
    @14
    cQ
    cU
    @38
    lsmlub
    syl3anc
    mpbi2and
    eqsstrd
    sstrd
    cC
    @2
    cQ
    vf
    cF
    @0
    cL
    c.pe
    lclkrslem1.c
    @5
    lcfls1c
    sylanbrc
end
