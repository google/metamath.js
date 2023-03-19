include "csin.mm"
include "cr.mm"
include "cres.mm"
include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "cv.mm"
include "cmul.mm"
include "cmpt.mm"
include "ccom.mm"
include "ccncf.mm"
include "cfv.mm"
include "wf.mm"
include "wceq.mm"
include "wcel.mm"
include "resincncf.mm"
include "cncff.mm"
include "ax-mp.mm"
include "wa.mm"
include "halfre.mm"
include "a1i.mm"
include "readdcld.mm"
include "adantr.mm"
include "wss.mm"
include "pire.mm"
include "renegcli.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sseli.mm"
include "adantl.mm"
include "remulcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "fcompt.mm"
include "sylancr.mm"
include "eqidd.mm"
include "oveq2.mm"
include "simpr.mm"
include "sseldi.mm"
include "fvmptd.mm"
include "fveq2d.mm"
include "mpteq2dva.mm"
include "fvres.mm"
include "syl.mm"
include "cbvmptv.mm"
include "3eqtrd.mm"
include "eqcomi.mm"
include "3eqtrrd.mm"
include "cc.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "recnd.mm"
include "halfcn.mm"
include "addcld.mm"
include "ssid.mm"
include "constcncfg.mm"
include "idcncfg.mm"
include "mulcncf.mm"
include "cncfmptssg.mm"
include "cncfco.mm"
include "eqeltrd.mm"

theorem fourierdlem18
  let wph: wff ph
  let cS: class S
  let cN: class N
  let vs: setvar s
  let vx: setvar x
  let vk: setvar k
  assume fourierdlem18.n: |- ( ph -> N e. RR )
  assume fourierdlem18.s: |- S = ( s e. ( -u _pi [,] _pi ) |-> ( sin ` ( ( N + ( 1 / 2 ) ) x. s ) ) )

  disjoint N s
  disjoint ph s
  disjoint N x
  disjoint s x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> S e. ( ( -u _pi [,] _pi ) -cn-> RR ) )

  proof
    wph
    cS
    csin
    cr
    cres
    #
    vs
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    cN
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    vs
    cv
    #
    cmul
    co
    #
    cmpt
    #
    ccom
    #
    @2
    cr
    ccncf
    co
    wph
    @8
    vx
    @2
    vx
    cv
    #
    @7
    cfv
    #
    @0
    cfv
    #
    cmpt
    #
    vs
    @2
    @6
    csin
    cfv
    #
    cmpt
    #
    cS
    wph
    cr
    cr
    @0
    wf
    #
    @2
    cr
    @7
    wf
    @8
    @12
    wceq
    @0
    cr
    cr
    ccncf
    co
    wcel
    #
    @15
    resincncf
    cr
    cr
    @0
    cncff
    ax-mp
    wph
    vs
    @2
    @6
    cr
    @7
    wph
    @5
    @2
    wcel
    #
    wa
    @4
    @5
    wph
    @4
    cr
    wcel
    #
    @17
    wph
    cN
    @3
    fourierdlem18.n
    @3
    cr
    wcel
    wph
    halfre
    a1i
    readdcld
    #
    adantr
    @17
    @5
    cr
    wcel
    wph
    @2
    cr
    @5
    @1
    cr
    wcel
    cpi
    cr
    wcel
    @2
    cr
    wss
    cpi
    pire
    renegcli
    pire
    @1
    cpi
    iccssre
    mp2an
    #
    sseli
    adantl
    remulcld
    #
    @7
    eqid
    #
    fmptd
    vx
    @0
    @7
    @2
    cr
    cr
    fcompt
    sylancr
    wph
    @12
    vx
    @2
    @4
    @9
    cmul
    co
    #
    @0
    cfv
    #
    cmpt
    vx
    @2
    @23
    csin
    cfv
    #
    cmpt
    #
    @14
    wph
    vx
    @2
    @11
    @24
    wph
    @9
    @2
    wcel
    #
    wa
    #
    @10
    @23
    @0
    @28
    vs
    @9
    @6
    @23
    @2
    @7
    cr
    @28
    @7
    eqidd
    @5
    @9
    wceq
    @6
    @23
    wceq
    @28
    @5
    @9
    @4
    cmul
    oveq2
    adantl
    wph
    @27
    simpr
    #
    @28
    @4
    @9
    wph
    @18
    @27
    @19
    adantr
    @28
    @2
    cr
    @9
    @20
    @29
    sseldi
    remulcld
    #
    fvmptd
    fveq2d
    mpteq2dva
    wph
    vx
    @2
    @24
    @25
    @28
    @23
    cr
    wcel
    @24
    @25
    wceq
    @30
    @23
    cr
    csin
    fvres
    syl
    mpteq2dva
    @26
    @14
    wceq
    wph
    vx
    vs
    @2
    @25
    @13
    @9
    @5
    wceq
    @23
    @6
    csin
    @9
    @5
    @4
    cmul
    oveq2
    fveq2d
    cbvmptv
    a1i
    3eqtrd
    @14
    cS
    wceq
    wph
    cS
    @14
    fourierdlem18.s
    eqcomi
    a1i
    3eqtrrd
    wph
    @2
    cr
    cr
    @7
    @0
    wph
    vs
    @2
    cc
    @2
    cr
    @6
    @7
    @22
    wph
    vs
    @4
    @5
    @2
    wph
    vs
    @2
    @4
    cc
    @2
    cc
    wss
    wph
    @2
    cr
    cc
    @20
    ax-resscn
    sstri
    a1i
    #
    wph
    cN
    @3
    wph
    cN
    fourierdlem18.n
    recnd
    @3
    cc
    wcel
    wph
    halfcn
    a1i
    addcld
    cc
    cc
    wss
    wph
    cc
    ssid
    a1i
    #
    constcncfg
    wph
    vs
    @2
    cc
    @31
    @32
    idcncfg
    mulcncf
    @2
    @2
    wss
    wph
    @2
    ssid
    a1i
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    @21
    cncfmptssg
    @16
    wph
    resincncf
    a1i
    cncfco
    eqeltrd
end
