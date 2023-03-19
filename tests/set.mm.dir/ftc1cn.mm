include "cioo.mm"
include "co.mm"
include "cr.mm"
include "cdv.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wfn.mm"
include "cc.mm"
include "wf.mm"
include "dvf.mm"
include "a1i.mm"
include "ffun.mm"
include "syl.mm"
include "cicc.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cnt.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "wss.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "ioossre.mm"
include "ccncf.mm"
include "wcel.mm"
include "cncff.mm"
include "ftc1lem2.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "eqid.mm"
include "tgioo2.mm"
include "dvbssntr.mm"
include "iccntr.mm"
include "sseqtrd.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "crest.mm"
include "adantr.mm"
include "cle.mm"
include "cibl.mm"
include "simpr.mm"
include "ccn.mm"
include "cuni.mm"
include "ccnp.mm"
include "sstri.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "mp2an.mm"
include "syl6eleq.mm"
include "ctopon.mm"
include "resttopon.mm"
include "sylancr.mm"
include "toponuni.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "cncnpi.mm"
include "ftc1.mm"
include "vex.mm"
include "fvex.mm"
include "breldm.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "df-fn.mm"
include "sylanbrc.mm"
include "ffn.mm"
include "funbrfv.mm"
include "sylc.mm"
include "eqfnfvd.mm"

theorem ftc1cn
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vy: setvar y
  assume ftc1cn.g: |- G = ( x e. ( A [,] B ) |-> S. ( A (,) x ) ( F ` t ) _d t )
  assume ftc1cn.a: |- ( ph -> A e. RR )
  assume ftc1cn.b: |- ( ph -> B e. RR )
  assume ftc1cn.le: |- ( ph -> A <_ B )
  assume ftc1cn.f: |- ( ph -> F e. ( ( A (,) B ) -cn-> CC ) )
  assume ftc1cn.i: |- ( ph -> F e. L^1 )

  disjoint t x
  disjoint A t
  disjoint A x
  disjoint B t
  disjoint B x
  disjoint F t
  disjoint F x
  disjoint ph t
  disjoint ph x
  disjoint t y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint G y
  disjoint ph y
  assert |- ( ph -> ( RR _D G ) = F )

  proof
    wph
    vy
    cA
    cB
    cioo
    co
    #
    cr
    cG
    cdv
    co
    #
    cF
    wph
    @1
    wfun
    #
    @1
    cdm
    #
    @0
    wceq
    @1
    @0
    wfn
    wph
    @3
    cc
    @1
    wf
    #
    @2
    @4
    wph
    cG
    dvf
    a1i
    @3
    cc
    @1
    ffun
    syl
    #
    wph
    @3
    @0
    wph
    @3
    cA
    cB
    cicc
    co
    #
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    @0
    wph
    @6
    cr
    cG
    @7
    ccnfld
    ctopn
    cfv
    #
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    wph
    vx
    vt
    cA
    cB
    @0
    cF
    cG
    ftc1cn.g
    ftc1cn.a
    ftc1cn.b
    ftc1cn.le
    @0
    @0
    wss
    #
    wph
    @0
    ssid
    #
    a1i
    @0
    cr
    wss
    #
    wph
    cA
    cB
    ioossre
    #
    a1i
    ftc1cn.i
    wph
    cF
    @0
    cc
    ccncf
    co
    #
    wcel
    @0
    cc
    cF
    wf
    #
    ftc1cn.f
    @0
    cc
    cF
    cncff
    syl
    #
    ftc1lem2
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @6
    cr
    wss
    ftc1cn.a
    ftc1cn.b
    cA
    cB
    iccssre
    syl2anc
    @9
    @9
    eqid
    #
    tgioo2
    #
    @19
    dvbssntr
    wph
    @17
    @18
    @8
    @0
    wceq
    ftc1cn.a
    ftc1cn.b
    cA
    cB
    iccntr
    syl2anc
    sseqtrd
    wph
    vy
    @0
    @3
    wph
    vy
    cv
    #
    @0
    wcel
    #
    @21
    @3
    wcel
    #
    wph
    @22
    wa
    #
    @21
    @21
    cF
    cfv
    #
    @1
    wbr
    #
    @23
    @24
    vx
    vt
    cA
    cB
    @21
    @0
    cF
    cG
    @7
    @9
    @0
    crest
    co
    #
    @9
    ftc1cn.g
    wph
    @17
    @22
    ftc1cn.a
    adantr
    wph
    @18
    @22
    ftc1cn.b
    adantr
    wph
    cA
    cB
    cle
    wbr
    @22
    ftc1cn.le
    adantr
    @10
    @24
    @11
    a1i
    @12
    @24
    @13
    a1i
    wph
    cF
    cibl
    wcel
    @22
    ftc1cn.i
    adantr
    wph
    @22
    simpr
    @24
    cF
    @27
    @9
    ccn
    co
    #
    wcel
    #
    @21
    @27
    cuni
    #
    wcel
    #
    cF
    @21
    @27
    @9
    ccnp
    co
    cfv
    wcel
    wph
    @29
    @22
    wph
    cF
    @14
    @28
    ftc1cn.f
    @0
    cc
    wss
    #
    cc
    cc
    wss
    @14
    @28
    wceq
    @0
    cr
    cc
    @13
    ax-resscn
    sstri
    #
    cc
    ssid
    @0
    cc
    @9
    @27
    @9
    @19
    @27
    eqid
    #
    @9
    cc
    crest
    co
    #
    @9
    @9
    ctop
    wcel
    @35
    @9
    wceq
    @9
    @19
    cnfldtop
    @9
    ctop
    cc
    cc
    @9
    @9
    @19
    cnfldtopon
    #
    toponunii
    restid
    ax-mp
    eqcomi
    cncfcn
    mp2an
    syl6eleq
    adantr
    wph
    @22
    @31
    wph
    @0
    @30
    @21
    wph
    @27
    @0
    ctopon
    cfv
    wcel
    #
    @0
    @30
    wceq
    wph
    @9
    cc
    ctopon
    cfv
    wcel
    @32
    @37
    @36
    @32
    wph
    @33
    a1i
    @0
    @9
    cc
    resttopon
    sylancr
    @0
    @27
    toponuni
    syl
    eleq2d
    biimpa
    @21
    cF
    @27
    @9
    @30
    @30
    eqid
    cncnpi
    syl2anc
    @20
    @34
    @19
    ftc1
    #
    @21
    @25
    @1
    vy
    vex
    @21
    cF
    fvex
    breldm
    syl
    ex
    ssrdv
    eqssd
    @1
    @0
    df-fn
    sylanbrc
    wph
    @15
    cF
    @0
    wfn
    @16
    @0
    cc
    cF
    ffn
    syl
    @24
    @2
    @26
    @21
    @1
    cfv
    @25
    wceq
    wph
    @2
    @22
    @5
    adantr
    @38
    @21
    @25
    @1
    funbrfv
    sylc
    eqfnfvd
end
