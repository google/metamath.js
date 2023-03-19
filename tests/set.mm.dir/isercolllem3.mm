include "c1.mm"
include "cfv.mm"
include "cuz.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cfz.mm"
include "co.mm"
include "cima.mm"
include "caddc.mm"
include "cc.mm"
include "cres.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "addid2.mm"
include "adantl.mm"
include "addid1.mm"
include "addcl.mm"
include "0cnd.mm"
include "chash.mm"
include "clt.mm"
include "wiso.mm"
include "cn.mm"
include "wss.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "adantr.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "isercolllem1.mm"
include "syldan.mm"
include "wb.mm"
include "isercolllem2.mm"
include "isoeq4.mm"
include "mpbird.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "a1i.mm"
include "sseqin2.mm"
include "sylib.mm"
include "1nn.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "syl6eleq.mm"
include "simpr.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "mpbir2and.mm"
include "ne0i.mm"
include "eqnetrd.mm"
include "imadisj.mm"
include "necon3bii.mm"
include "sylibr.mm"
include "crn.mm"
include "wfun.mm"
include "ffun.mm"
include "funimacnv.mm"
include "inss1.mm"
include "eqsstrd.mm"
include "simpl.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "syl2an.mm"
include "cdif.mm"
include "difeq2d.mm"
include "difin.mm"
include "syl6eq.mm"
include "ssriv.mm"
include "ssdif.mm"
include "mp1i.mm"
include "sselda.mm"
include "adantlr.mm"
include "elfznn.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "fvres.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "seqcoll2.mm"

theorem isercolllem3
  let wph: wff ph
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vj: setvar j
  let vm: setvar m
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cS: class S
  assume isercoll.z: |- Z = ( ZZ>= ` M )
  assume isercoll.m: |- ( ph -> M e. ZZ )
  assume isercoll.g: |- ( ph -> G : NN --> Z )
  assume isercoll.i: |- ( ( ph /\ k e. NN ) -> ( G ` k ) < ( G ` ( k + 1 ) ) )
  assume isercoll.0: |- ( ( ph /\ n e. ( Z \ ran G ) ) -> ( F ` n ) = 0 )
  assume isercoll.f: |- ( ( ph /\ n e. Z ) -> ( F ` n ) e. CC )
  assume isercoll.h: |- ( ( ph /\ k e. NN ) -> ( H ` k ) = ( F ` ( G ` k ) ) )

  disjoint k n
  disjoint F k
  disjoint F n
  disjoint N k
  disjoint N n
  disjoint k ph
  disjoint n ph
  disjoint G k
  disjoint G n
  disjoint H k
  disjoint H n
  disjoint M k
  disjoint M n
  disjoint Z n
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint A j
  disjoint k m
  disjoint k x
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint F j
  disjoint F m
  disjoint F x
  disjoint k y
  disjoint n y
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint j y
  disjoint j ph
  disjoint m y
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint G j
  disjoint G m
  disjoint G x
  disjoint G y
  disjoint H j
  disjoint H m
  disjoint H x
  disjoint M j
  disjoint M m
  disjoint M x
  disjoint M y
  disjoint S x
  disjoint S y
  assert |- ( ( ph /\ N e. ( ZZ>= ` ( G ` 1 ) ) ) -> ( seq M ( + , F ) ` N ) = ( seq 1 ( + , H ) ` ( # ` ( G " ( `' G " ( M ... N ) ) ) ) ) )

  proof
    wph
    cN
    c1
    cG
    cfv
    #
    cuz
    cfv
    wcel
    #
    wa
    #
    cG
    cG
    ccnv
    cM
    cN
    cfz
    co
    #
    cima
    #
    cima
    #
    caddc
    cc
    vn
    vk
    cF
    cG
    @4
    cres
    #
    cH
    cM
    cN
    cc0
    vn
    cv
    #
    cc
    wcel
    #
    cc0
    @7
    caddc
    co
    @7
    wceq
    @2
    @7
    addid2
    adantl
    @8
    @7
    cc0
    caddc
    co
    @7
    wceq
    @2
    @7
    addid1
    adantl
    @8
    vk
    cv
    #
    cc
    wcel
    wa
    @7
    @9
    caddc
    co
    cc
    wcel
    @2
    @7
    @9
    addcl
    adantl
    @2
    0cnd
    @2
    c1
    @5
    chash
    cfv
    #
    cfz
    co
    #
    @5
    clt
    clt
    @6
    wiso
    #
    @4
    @5
    clt
    clt
    @6
    wiso
    #
    wph
    @1
    @4
    cn
    wss
    @13
    @2
    cG
    cdm
    #
    @4
    cn
    cG
    @3
    cnvimass
    #
    @2
    cn
    cZ
    cG
    wf
    #
    @14
    cn
    wceq
    wph
    @16
    @1
    isercoll.g
    adantr
    #
    cn
    cZ
    cG
    fdm
    syl
    syl5sseq
    wph
    @4
    vk
    cG
    cM
    cZ
    isercoll.z
    isercoll.m
    isercoll.g
    isercoll.i
    isercolllem1
    syldan
    @2
    @11
    @4
    wceq
    @12
    @13
    wb
    wph
    vk
    cG
    cM
    cN
    cZ
    isercoll.z
    isercoll.m
    isercoll.g
    isercoll.i
    isercolllem2
    #
    @11
    @5
    @4
    clt
    clt
    @6
    isoeq4
    syl
    mpbird
    @2
    @14
    @4
    cin
    #
    c0
    wne
    @5
    c0
    wne
    @2
    @19
    @4
    c0
    @2
    @4
    @14
    wss
    #
    @19
    @4
    wceq
    @20
    @2
    @15
    a1i
    @4
    @14
    sseqin2
    sylib
    @2
    c1
    @4
    wcel
    #
    @4
    c0
    wne
    @2
    @21
    c1
    cn
    wcel
    #
    @0
    @3
    wcel
    #
    @22
    @2
    1nn
    a1i
    @2
    @0
    cM
    cuz
    cfv
    #
    wcel
    #
    @1
    @23
    wph
    @25
    @1
    wph
    @0
    cZ
    @24
    wph
    @16
    @22
    @0
    cZ
    wcel
    isercoll.g
    1nn
    cn
    cZ
    c1
    cG
    ffvelrn
    sylancl
    isercoll.z
    syl6eleq
    adantr
    wph
    @1
    simpr
    @0
    cM
    cN
    elfzuzb
    sylanbrc
    @2
    @16
    cG
    cn
    wfn
    @21
    @22
    @23
    wa
    wb
    @17
    cn
    cZ
    cG
    ffn
    cn
    c1
    @3
    cG
    elpreima
    3syl
    mpbir2and
    @4
    c1
    ne0i
    syl
    eqnetrd
    @5
    c0
    @19
    c0
    cG
    @4
    imadisj
    necon3bii
    sylibr
    @2
    @5
    @3
    cG
    crn
    #
    cin
    #
    @3
    @2
    @16
    cG
    wfun
    @5
    @27
    wceq
    @17
    cn
    cZ
    cG
    ffun
    @3
    cG
    funimacnv
    3syl
    #
    @27
    @3
    wss
    @2
    @3
    @26
    inss1
    a1i
    eqsstrd
    @2
    wph
    @7
    cZ
    wcel
    @7
    cF
    cfv
    #
    cc
    wcel
    @7
    @3
    wcel
    #
    wph
    @1
    simpl
    #
    @30
    @7
    @24
    cZ
    @7
    cM
    cN
    elfzuz
    isercoll.z
    syl6eleqr
    #
    isercoll.f
    syl2an
    @2
    @7
    @3
    @5
    cdif
    #
    wcel
    @7
    cZ
    @26
    cdif
    #
    wcel
    #
    @29
    cc0
    wceq
    #
    @2
    @33
    @34
    @7
    @2
    @33
    @3
    @26
    cdif
    #
    @34
    @2
    @33
    @3
    @27
    cdif
    @37
    @2
    @5
    @27
    @3
    @28
    difeq2d
    @3
    @26
    difin
    syl6eq
    @3
    cZ
    wss
    @37
    @34
    wss
    @2
    vn
    @3
    cZ
    @32
    ssriv
    @3
    cZ
    @26
    ssdif
    mp1i
    eqsstrd
    sselda
    wph
    @35
    @36
    @1
    isercoll.0
    adantlr
    syldan
    @2
    @9
    @11
    wcel
    #
    wa
    #
    @9
    cH
    cfv
    #
    @9
    cG
    cfv
    #
    cF
    cfv
    #
    @9
    @6
    cfv
    #
    cF
    cfv
    @2
    wph
    @9
    cn
    wcel
    @40
    @42
    wceq
    @38
    @31
    @9
    @10
    elfznn
    isercoll.h
    syl2an
    @39
    @43
    @41
    cF
    @39
    @9
    @4
    wcel
    #
    @43
    @41
    wceq
    @2
    @38
    @44
    @2
    @11
    @4
    @9
    @18
    eleq2d
    biimpa
    @9
    @4
    cG
    fvres
    syl
    fveq2d
    eqtr4d
    seqcoll2
end
