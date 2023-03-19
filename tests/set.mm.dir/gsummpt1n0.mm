include "cgsu.mm"
include "co.mm"
include "cfv.mm"
include "csb.mm"
include "cbs.mm"
include "eqid.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "wcel.mm"
include "wa.mm"
include "r19.21bi.mm"
include "cmnd.mm"
include "mndidcl.mm"
include "syl.mm"
include "adantr.mm"
include "ifcld.mm"
include "fmptd.mm"
include "csupp.mm"
include "cmpt.mm"
include "csn.mm"
include "oveq1i.mm"
include "cdif.mm"
include "wne.mm"
include "eldifsni.mm"
include "adantl.mm"
include "ifnefalse.mm"
include "suppss2.mm"
include "syl5eqss.mm"
include "gsumpt.mm"
include "wral.mm"
include "rspcsbela.mm"
include "syl2anc.mm"
include "iftrue.mm"
include "csbeq1.mm"
include "eqtrd.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfif.mm"
include "weq.mm"
include "eqeq1.mm"
include "csbeq1a.mm"
include "ifbieq1d.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "fvmptg.mm"

theorem gsummpt1n0
  let wph: wff ph
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cI: class I
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vy: setvar y
  assume gsummpt1n0.0: |- .0. = ( 0g ` G )
  assume gsummpt1n0.g: |- ( ph -> G e. Mnd )
  assume gsummpt1n0.i: |- ( ph -> I e. W )
  assume gsummpt1n0.x: |- ( ph -> X e. I )
  assume gsummpt1n0.f: |- F = ( n e. I |-> if ( n = X , A , .0. ) )
  assume gsummpt1n0.a: |- ( ph -> A. n e. I A e. ( Base ` G ) )

  disjoint I n
  disjoint G n
  disjoint I n
  disjoint X n
  disjoint n ph
  disjoint .0. n
  disjoint A y
  disjoint I y
  disjoint n y
  disjoint X y
  disjoint .0. y
  assert |- ( ph -> ( G gsum F ) = [_ X / n ]_ A )

  proof
    wph
    cG
    cF
    cgsu
    co
    cX
    cF
    cfv
    #
    vn
    cX
    cA
    csb
    #
    wph
    cI
    cG
    cbs
    cfv
    #
    cF
    cG
    cW
    cX
    c.0
    @2
    eqid
    #
    gsummpt1n0.0
    gsummpt1n0.g
    gsummpt1n0.i
    gsummpt1n0.x
    wph
    vn
    cI
    vn
    cv
    #
    cX
    wceq
    #
    cA
    c.0
    cif
    #
    @2
    cF
    wph
    @4
    cI
    wcel
    #
    wa
    @5
    cA
    c.0
    @2
    wph
    cA
    @2
    wcel
    #
    vn
    cI
    gsummpt1n0.a
    r19.21bi
    wph
    c.0
    @2
    wcel
    #
    @7
    wph
    cG
    cmnd
    wcel
    @9
    gsummpt1n0.g
    @2
    cG
    c.0
    @3
    gsummpt1n0.0
    mndidcl
    syl
    adantr
    ifcld
    gsummpt1n0.f
    fmptd
    wph
    cF
    c.0
    csupp
    co
    vn
    cI
    @6
    cmpt
    #
    c.0
    csupp
    co
    cX
    csn
    #
    cF
    @10
    c.0
    csupp
    gsummpt1n0.f
    oveq1i
    wph
    cI
    @6
    vn
    cW
    @11
    c.0
    wph
    @4
    cI
    @11
    cdif
    wcel
    #
    wa
    @4
    cX
    wne
    #
    @6
    c.0
    wceq
    @12
    @13
    wph
    @4
    cI
    cX
    eldifsni
    adantl
    @4
    cX
    cA
    c.0
    ifnefalse
    syl
    gsummpt1n0.i
    suppss2
    syl5eqss
    gsumpt
    wph
    cX
    cI
    wcel
    #
    @1
    @2
    wcel
    #
    @0
    @1
    wceq
    gsummpt1n0.x
    wph
    @14
    @8
    vn
    cI
    wral
    @15
    gsummpt1n0.x
    gsummpt1n0.a
    vn
    cX
    cI
    cA
    @2
    rspcsbela
    syl2anc
    vy
    cX
    vy
    cv
    #
    cX
    wceq
    #
    vn
    @16
    cA
    csb
    #
    c.0
    cif
    #
    @1
    cI
    @2
    cF
    @17
    @19
    @18
    @1
    @17
    @18
    c.0
    iftrue
    vn
    @16
    cX
    cA
    csbeq1
    eqtrd
    cF
    @10
    vy
    cI
    @19
    cmpt
    gsummpt1n0.f
    vn
    vy
    cI
    @6
    @19
    vy
    @6
    nfcv
    @17
    vn
    @18
    c.0
    @17
    vn
    nfv
    vn
    @16
    cA
    nfcsb1v
    vn
    c.0
    nfcv
    nfif
    vn
    vy
    weq
    @5
    @17
    cA
    @18
    c.0
    @4
    @16
    cX
    eqeq1
    vn
    @16
    cA
    csbeq1a
    ifbieq1d
    cbvmpt
    eqtri
    fvmptg
    syl2anc
    eqtrd
end
