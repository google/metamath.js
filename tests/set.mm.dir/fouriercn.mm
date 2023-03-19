include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cpi.mm"
include "cneg.mm"
include "co.mm"
include "cdm.mm"
include "cdif.mm"
include "c0.mm"
include "cfn.mm"
include "cr.mm"
include "cdv.mm"
include "cres.mm"
include "dmeqi.mm"
include "wss.mm"
include "wceq.mm"
include "ioossre.mm"
include "cc.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "cncff.mm"
include "fdm.mm"
include "3syl.mm"
include "syl5sseqr.mm"
include "ssdmres.mm"
include "sylib.mm"
include "syl5eq.mm"
include "difeq2d.mm"
include "difid.mm"
include "syl6eq.mm"
include "0fin.mm"
include "syl6eqel.mm"
include "rescncf.mm"
include "mpsyl.mm"
include "a1i.mm"
include "oveq1d.mm"
include "3eltr4d.mm"
include "cv.mm"
include "cico.mm"
include "cpnf.mm"
include "climc.mm"
include "wne.mm"
include "cxr.mm"
include "pire.mm"
include "renegcli.mm"
include "rexri.mm"
include "icossre.mm"
include "mp2an.mm"
include "eldifi.mm"
include "sseldi.mm"
include "wa.mm"
include "cin.mm"
include "limcresi.mm"
include "reseq1i.mm"
include "resres.mm"
include "eqtr2i.mm"
include "oveq1i.mm"
include "sseqtri.mm"
include "adantr.mm"
include "simpr.mm"
include "cnlimci.mm"
include "ne0i.mm"
include "syl.mm"
include "sylan2.mm"
include "cioc.mm"
include "cmnf.mm"
include "negpitopissre.mm"
include "eqid.mm"
include "ccn.mm"
include "ccnp.mm"
include "wb.mm"
include "ax-resscn.mm"
include "fssd.mm"
include "ssid.mm"
include "dvcn.mm"
include "syl31anc.mm"
include "cncffvrn.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "tgioo2.mm"
include "cncfcn.mm"
include "eleqtrd.mm"
include "uniretop.mm"
include "cncnpi.mm"
include "fouriercnp.mm"

theorem fouriercn
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cX: class X
  let vk: setvar k
  assume fouriercn.f: |- ( ph -> F : RR --> RR )
  assume fouriercn.t: |- T = ( 2 x. _pi )
  assume fouriercn.per: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fouriercn.dv: |- ( ph -> ( RR _D F ) e. ( RR -cn-> CC ) )
  assume fouriercn.g: |- G = ( ( RR _D F ) |` ( -u _pi (,) _pi ) )
  assume fouriercn.x: |- ( ph -> X e. RR )
  assume fouriercn.a: |- A = ( n e. NN0 |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( cos ` ( n x. x ) ) ) _d x / _pi ) )
  assume fouriercn.b: |- B = ( n e. NN |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( sin ` ( n x. x ) ) ) _d x / _pi ) )

  disjoint F n
  disjoint F x
  disjoint n x
  disjoint G x
  disjoint T x
  disjoint X n
  disjoint X x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( ( A ` 0 ) / 2 ) + sum_ n e. NN ( ( ( A ` n ) x. ( cos ` ( n x. X ) ) ) + ( ( B ` n ) x. ( sin ` ( n x. X ) ) ) ) ) = ( F ` X ) )

  proof
    wph
    vx
    cA
    cB
    cT
    vn
    cF
    cG
    cioo
    crn
    ctg
    cfv
    #
    cX
    fouriercn.f
    fouriercn.t
    fouriercn.per
    fouriercn.g
    wph
    cpi
    cneg
    #
    cpi
    cioo
    co
    #
    cG
    cdm
    #
    cdif
    #
    c0
    cfn
    wph
    @4
    @2
    @2
    cdif
    c0
    wph
    @3
    @2
    @2
    wph
    @3
    cr
    cF
    cdv
    co
    #
    @2
    cres
    #
    cdm
    #
    @2
    cG
    @6
    fouriercn.g
    dmeqi
    wph
    @2
    @5
    cdm
    #
    wss
    @7
    @2
    wceq
    wph
    cr
    @2
    @8
    @1
    cpi
    ioossre
    #
    wph
    @5
    cr
    cc
    ccncf
    co
    #
    wcel
    #
    cr
    cc
    @5
    wf
    @8
    cr
    wceq
    #
    fouriercn.dv
    cr
    cc
    @5
    cncff
    cr
    cc
    @5
    fdm
    3syl
    #
    syl5sseqr
    @2
    @5
    ssdmres
    sylib
    syl5eq
    #
    difeq2d
    @2
    difid
    syl6eq
    0fin
    syl6eqel
    wph
    @6
    @2
    cc
    ccncf
    co
    #
    cG
    @3
    cc
    ccncf
    co
    @2
    cr
    wss
    wph
    @11
    @6
    @15
    wcel
    @9
    fouriercn.dv
    cr
    cc
    @2
    @5
    rescncf
    mpsyl
    cG
    @6
    wceq
    wph
    fouriercn.g
    a1i
    wph
    @3
    @2
    cc
    ccncf
    @14
    oveq1d
    3eltr4d
    vx
    cv
    #
    @1
    cpi
    cico
    co
    #
    @3
    cdif
    wcel
    #
    wph
    @16
    cr
    wcel
    #
    cG
    @16
    cpnf
    cioo
    co
    #
    cres
    #
    @16
    climc
    co
    #
    c0
    wne
    #
    @18
    @17
    cr
    @16
    @1
    cr
    wcel
    cpi
    cxr
    wcel
    @17
    cr
    wss
    cpi
    pire
    renegcli
    cpi
    pire
    rexri
    @1
    cpi
    icossre
    mp2an
    @16
    @17
    @3
    eldifi
    sseldi
    wph
    @19
    wa
    #
    @16
    @5
    cfv
    #
    @22
    wcel
    @23
    @24
    @5
    @16
    climc
    co
    #
    @22
    @25
    @26
    @5
    @2
    @20
    cin
    #
    cres
    #
    @16
    climc
    co
    @22
    @16
    @27
    @5
    limcresi
    @28
    @21
    @16
    climc
    @21
    @6
    @20
    cres
    @28
    cG
    @6
    @20
    fouriercn.g
    reseq1i
    @5
    @2
    @20
    resres
    eqtr2i
    oveq1i
    sseqtri
    @24
    cr
    @16
    cc
    @5
    wph
    @11
    @19
    fouriercn.dv
    adantr
    wph
    @19
    simpr
    cnlimci
    #
    sseldi
    @22
    @25
    ne0i
    syl
    sylan2
    @16
    @1
    cpi
    cioc
    co
    #
    @3
    cdif
    wcel
    #
    wph
    @19
    cG
    cmnf
    @16
    cioo
    co
    #
    cres
    #
    @16
    climc
    co
    #
    c0
    wne
    #
    @31
    @30
    cr
    @16
    negpitopissre
    @16
    @30
    @3
    eldifi
    sseldi
    @24
    @25
    @34
    wcel
    @35
    @24
    @26
    @34
    @25
    @26
    @5
    @2
    @32
    cin
    #
    cres
    #
    @16
    climc
    co
    @34
    @16
    @36
    @5
    limcresi
    @37
    @33
    @16
    climc
    @33
    @6
    @32
    cres
    @37
    cG
    @6
    @32
    fouriercn.g
    reseq1i
    @5
    @2
    @32
    resres
    eqtr2i
    oveq1i
    sseqtri
    @29
    sseldi
    @34
    @25
    ne0i
    syl
    sylan2
    @0
    eqid
    wph
    cF
    @0
    @0
    ccn
    co
    #
    wcel
    cX
    cr
    wcel
    cF
    cX
    @0
    @0
    ccnp
    co
    cfv
    wcel
    wph
    cF
    cr
    cr
    ccncf
    co
    #
    @38
    wph
    cF
    @39
    wcel
    #
    cr
    cr
    cF
    wf
    #
    fouriercn.f
    wph
    cr
    cc
    wss
    #
    cF
    @10
    wcel
    #
    @40
    @41
    wb
    @42
    wph
    ax-resscn
    a1i
    #
    wph
    @42
    cr
    cc
    cF
    wf
    cr
    cr
    wss
    #
    @12
    @43
    @44
    wph
    cr
    cr
    cc
    cF
    fouriercn.f
    @44
    fssd
    @45
    wph
    cr
    ssid
    a1i
    @13
    cr
    cr
    cF
    dvcn
    syl31anc
    cr
    cc
    cr
    cF
    cncffvrn
    syl2anc
    mpbird
    wph
    @42
    @42
    @39
    @38
    wceq
    @44
    @44
    cr
    cr
    ccnfld
    ctopn
    cfv
    #
    @0
    @0
    @46
    eqid
    #
    @46
    @47
    tgioo2
    #
    @48
    cncfcn
    syl2anc
    eleqtrd
    fouriercn.x
    cX
    cF
    @0
    @0
    cr
    uniretop
    cncnpi
    syl2anc
    fouriercn.a
    fouriercn.b
    fouriercnp
end
