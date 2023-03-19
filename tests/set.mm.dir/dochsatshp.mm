include "cfv.mm"
include "wcel.mm"
include "clss.mm"
include "cbs.mm"
include "wne.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "clspn.mm"
include "wceq.mm"
include "wrex.mm"
include "chlt.mm"
include "wa.mm"
include "wss.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lsatssv.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "c0g.mm"
include "lsatn0.mm"
include "doch0.mm"
include "syl.mm"
include "eqeq2d.mm"
include "cdih.mm"
include "crn.mm"
include "dih1dimat.mm"
include "dih0rn.mm"
include "doch11.mm"
include "bitr3d.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "cdif.mm"
include "clmod.mm"
include "wb.mm"
include "islsat.mm"
include "mpbid.mm"
include "wi.mm"
include "eldifi.mm"
include "adantr.mm"
include "a1i.mm"
include "lspid.mm"
include "uneq1d.mm"
include "fveq2d.mm"
include "lssss.mm"
include "snssd.mm"
include "adantl.mm"
include "lspun.mm"
include "syl3anc.mm"
include "uneq2.mm"
include "3eqtr4d.mm"
include "cdjh.mm"
include "co.mm"
include "clsm.mm"
include "dochcl.mm"
include "dihjat2.mm"
include "djhcom.mm"
include "lsatlssel.mm"
include "lsmsp.mm"
include "3eqtr3rd.mm"
include "djhexmid.mm"
include "eqtrd.mm"
include "ex.mm"
include "jcad.mm"
include "reximdv2.mm"
include "mpd.mm"
include "clvec.mm"
include "w3a.mm"
include "dvhlvec.mm"
include "islshp.mm"
include "mpbir3and.mm"

theorem dochsatshp
  let wph: wff ph
  let cA: class A
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cY: class Y
  let vv: setvar v
  assume dochsatshp.h: |- H = ( LHyp ` K )
  assume dochsatshp.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochsatshp.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochsatshp.a: |- A = ( LSAtoms ` U )
  assume dochsatshp.y: |- Y = ( LSHyp ` U )
  assume dochsatshp.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochsatshp.q: |- ( ph -> Q e. A )


  assert |- ( ph -> ( ._|_ ` Q ) e. Y )

  proof
    wph
    cQ
    c.pe
    cfv
    #
    cY
    wcel
    #
    @0
    cU
    clss
    cfv
    #
    wcel
    #
    @0
    cU
    cbs
    cfv
    #
    wne
    #
    @0
    vv
    cv
    #
    csn
    #
    cun
    cU
    clspn
    cfv
    #
    cfv
    #
    @4
    wceq
    #
    vv
    @4
    wrex
    #
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cQ
    @4
    wss
    #
    @3
    dochsatshp.k
    wph
    cA
    cQ
    @4
    cU
    @4
    eqid
    #
    dochsatshp.a
    wph
    cU
    cH
    cK
    cW
    dochsatshp.h
    dochsatshp.u
    dochsatshp.k
    dvhlmod
    #
    dochsatshp.q
    lsatssv
    #
    @2
    cU
    cH
    cK
    c.pe
    @4
    cW
    cQ
    dochsatshp.h
    dochsatshp.u
    @14
    @2
    eqid
    #
    dochsatshp.o
    dochlss
    syl2anc
    #
    wph
    @5
    cQ
    cU
    c0g
    cfv
    #
    csn
    #
    wne
    wph
    cA
    cQ
    cU
    @19
    @19
    eqid
    #
    dochsatshp.a
    @15
    dochsatshp.q
    lsatn0
    wph
    @0
    @4
    cQ
    @20
    wph
    @0
    @20
    c.pe
    cfv
    #
    wceq
    @0
    @4
    wceq
    cQ
    @20
    wceq
    wph
    @22
    @4
    @0
    wph
    @12
    @22
    @4
    wceq
    dochsatshp.k
    cU
    cH
    cK
    c.pe
    @4
    cW
    @19
    dochsatshp.h
    dochsatshp.u
    dochsatshp.o
    @14
    @21
    doch0
    syl
    eqeq2d
    wph
    cH
    cW
    cK
    cdih
    cfv
    cfv
    #
    cK
    c.pe
    cW
    cQ
    @20
    dochsatshp.h
    @23
    eqid
    #
    dochsatshp.o
    dochsatshp.k
    wph
    @12
    cQ
    cA
    wcel
    #
    cQ
    @23
    crn
    #
    wcel
    dochsatshp.k
    dochsatshp.q
    cA
    cQ
    cU
    cH
    @23
    cK
    cW
    dochsatshp.h
    dochsatshp.u
    @24
    dochsatshp.a
    dih1dimat
    syl2anc
    wph
    @12
    @20
    @26
    wcel
    dochsatshp.k
    cU
    cH
    @23
    cK
    cW
    @19
    dochsatshp.h
    @24
    dochsatshp.u
    @21
    dih0rn
    syl
    doch11
    bitr3d
    necon3bid
    mpbird
    wph
    cQ
    @7
    @8
    cfv
    #
    wceq
    #
    vv
    @4
    @20
    cdif
    #
    wrex
    #
    @11
    wph
    @25
    @30
    dochsatshp.q
    wph
    cU
    clmod
    wcel
    #
    @25
    @30
    wb
    @15
    vv
    cA
    cQ
    @8
    @4
    cU
    clmod
    @19
    @14
    @8
    eqid
    #
    @21
    dochsatshp.a
    islsat
    syl
    mpbid
    wph
    @28
    @10
    vv
    @29
    @4
    wph
    @6
    @29
    wcel
    #
    @28
    wa
    #
    @6
    @4
    wcel
    #
    @10
    @34
    @35
    wi
    wph
    @33
    @35
    @28
    @6
    @4
    @20
    eldifi
    #
    adantr
    a1i
    wph
    @34
    @10
    wph
    @34
    wa
    #
    @9
    @0
    cQ
    cun
    #
    @8
    cfv
    #
    @4
    @37
    @0
    @8
    cfv
    #
    @27
    cun
    #
    @8
    cfv
    #
    @0
    @27
    cun
    #
    @8
    cfv
    #
    @9
    @39
    wph
    @42
    @44
    wceq
    @34
    wph
    @41
    @43
    @8
    wph
    @40
    @0
    @27
    wph
    @31
    @3
    @40
    @0
    wceq
    @15
    @18
    @2
    @0
    @8
    cU
    @17
    @32
    lspid
    syl2anc
    uneq1d
    fveq2d
    adantr
    @37
    @31
    @0
    @4
    wss
    #
    @7
    @4
    wss
    #
    @9
    @42
    wceq
    wph
    @31
    @34
    @15
    adantr
    wph
    @45
    @34
    wph
    @3
    @45
    @18
    @2
    @0
    @4
    cU
    @14
    @17
    lssss
    syl
    #
    adantr
    @34
    @46
    wph
    @33
    @46
    @28
    @33
    @6
    @4
    @36
    snssd
    adantr
    adantl
    @0
    @7
    @8
    @4
    cU
    @14
    @32
    lspun
    syl3anc
    @34
    @39
    @44
    wceq
    #
    wph
    @28
    @48
    @33
    @28
    @38
    @43
    @8
    cQ
    @27
    @0
    uneq2
    fveq2d
    adantl
    adantl
    3eqtr4d
    wph
    @39
    @4
    wceq
    @34
    wph
    @39
    cQ
    @0
    cW
    cK
    cdjh
    cfv
    cfv
    #
    co
    #
    @4
    wph
    @0
    cQ
    @49
    co
    @0
    cQ
    cU
    clsm
    cfv
    #
    co
    #
    @50
    @39
    wph
    cA
    @51
    cQ
    cU
    cH
    @23
    @49
    cK
    cW
    @0
    dochsatshp.h
    @24
    @49
    eqid
    #
    dochsatshp.u
    @51
    eqid
    #
    dochsatshp.a
    dochsatshp.k
    wph
    @12
    @13
    @0
    @26
    wcel
    dochsatshp.k
    @16
    cU
    cH
    @23
    cK
    c.pe
    @4
    cW
    cQ
    dochsatshp.h
    @24
    dochsatshp.u
    @14
    dochsatshp.o
    dochcl
    syl2anc
    dochsatshp.q
    dihjat2
    wph
    cU
    cH
    @49
    cK
    @4
    cW
    @0
    cQ
    dochsatshp.h
    dochsatshp.u
    @14
    @53
    dochsatshp.k
    @47
    @16
    djhcom
    wph
    @31
    @3
    cQ
    @2
    wcel
    @52
    @39
    wceq
    @15
    @18
    wph
    cA
    @2
    cQ
    cU
    @17
    dochsatshp.a
    @15
    dochsatshp.q
    lsatlssel
    @51
    @2
    @0
    cQ
    @8
    cU
    @17
    @32
    @54
    lsmsp
    syl3anc
    3eqtr3rd
    wph
    @12
    @13
    @50
    @4
    wceq
    dochsatshp.k
    @16
    cU
    cH
    @49
    cK
    c.pe
    @4
    cW
    cQ
    dochsatshp.h
    dochsatshp.u
    @14
    dochsatshp.o
    @53
    djhexmid
    syl2anc
    eqtrd
    adantr
    eqtrd
    ex
    jcad
    reximdv2
    mpd
    wph
    cU
    clvec
    wcel
    @1
    @3
    @5
    @11
    w3a
    wb
    wph
    cU
    cH
    cK
    cW
    dochsatshp.h
    dochsatshp.u
    dochsatshp.k
    dvhlvec
    vv
    @2
    @0
    cY
    @8
    @4
    cU
    clvec
    @14
    @32
    @17
    dochsatshp.y
    islshp
    syl
    mpbir3and
end
