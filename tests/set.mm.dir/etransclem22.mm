include "cfv.mm"
include "cdvn.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "cif.mm"
include "clt.mm"
include "wbr.mm"
include "cfa.mm"
include "cdiv.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "cmpt.mm"
include "cc.mm"
include "ccncf.mm"
include "etransclem17.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "iftrued.mm"
include "mpteq2dv.mm"
include "dvdmsscn.mm"
include "0cnd.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "constcncfg.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "wn.mm"
include "iffalsed.mm"
include "nfv.mm"
include "idcncfg.mm"
include "elfzelzd.mm"
include "zcnd.mm"
include "subcncf.mm"
include "cn0.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nnnn0d.mm"
include "ifcld.mm"
include "faccld.mm"
include "nncnd.mm"
include "cz.mm"
include "cle.mm"
include "nn0zd.mm"
include "zsubcld.mm"
include "cr.mm"
include "nn0red.mm"
include "nltled.mm"
include "subge0d.mm"
include "mpbird.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "nnne0d.mm"
include "divcld.mm"
include "expcncf.mm"
include "mulcncf.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "cncfcompt2.mm"
include "pm2.61dan.mm"

theorem etransclem22
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cS: class S
  let vj: setvar j
  let cH: class H
  let cJ: class J
  let cM: class M
  let cN: class N
  let cX: class X
  let vy: setvar y
  let vk: setvar k
  assume etransclem22.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem22.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem22.p: |- ( ph -> P e. NN )
  assume etransclem22.h: |- H = ( j e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) )
  assume etransclem22.J: |- ( ph -> J e. ( 0 ... M ) )
  assume etransclem22.n: |- ( ph -> N e. NN0 )

  disjoint J j
  disjoint J x
  disjoint j x
  disjoint M j
  disjoint M x
  disjoint N x
  disjoint P j
  disjoint P x
  disjoint S x
  disjoint X j
  disjoint X x
  disjoint j ph
  disjoint ph x
  disjoint J y
  disjoint x y
  disjoint N y
  disjoint P y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( ( S Dn ( H ` J ) ) ` N ) e. ( X -cn-> CC ) )

  proof
    wph
    cN
    cS
    cJ
    cH
    cfv
    cdvn
    co
    cfv
    vx
    cX
    cJ
    cc0
    wceq
    #
    cP
    c1
    cmin
    co
    #
    cP
    cif
    #
    cN
    clt
    wbr
    #
    cc0
    @2
    cfa
    cfv
    #
    @2
    cN
    cmin
    co
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    vx
    cv
    #
    cJ
    cmin
    co
    #
    @5
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    cmpt
    #
    cX
    cc
    ccncf
    co
    #
    wph
    vx
    cP
    cS
    vj
    cH
    cJ
    cM
    cN
    cX
    etransclem22.s
    etransclem22.x
    etransclem22.p
    etransclem22.h
    etransclem22.J
    etransclem22.n
    etransclem17
    wph
    @3
    @13
    @14
    wcel
    wph
    @3
    wa
    #
    @13
    vx
    cX
    cc0
    cmpt
    #
    @14
    @15
    vx
    cX
    @12
    cc0
    @15
    @3
    cc0
    @11
    wph
    @3
    simpr
    iftrued
    mpteq2dv
    wph
    @16
    @14
    wcel
    @3
    wph
    vx
    cX
    cc0
    cc
    wph
    cS
    cX
    etransclem22.s
    etransclem22.x
    dvdmsscn
    #
    wph
    0cnd
    cc
    cc
    wss
    #
    wph
    cc
    ssid
    #
    a1i
    #
    constcncfg
    adantr
    eqeltrd
    wph
    @3
    wn
    #
    wa
    #
    @13
    vx
    cX
    @11
    cmpt
    @14
    @22
    vx
    cX
    @12
    @11
    @22
    @3
    cc0
    @11
    wph
    @21
    simpr
    #
    iffalsed
    mpteq2dv
    @22
    vx
    vy
    cX
    cc
    cc
    @9
    @7
    vy
    cv
    #
    @5
    cexp
    co
    #
    cmul
    co
    @11
    cc
    @22
    vx
    nfv
    wph
    vx
    cX
    @9
    cmpt
    @14
    wcel
    @21
    wph
    vx
    @8
    cJ
    cX
    wph
    vx
    cX
    cc
    @17
    @20
    idcncfg
    wph
    vx
    cX
    cJ
    cc
    @17
    wph
    cJ
    wph
    cJ
    cc0
    cM
    etransclem22.J
    elfzelzd
    zcnd
    @20
    constcncfg
    subcncf
    adantr
    @22
    vy
    @7
    @25
    cc
    @22
    vy
    cc
    @7
    cc
    @18
    @22
    @19
    a1i
    #
    @22
    @4
    @6
    wph
    @4
    cc
    wcel
    @21
    wph
    @4
    wph
    @2
    wph
    @0
    @1
    cP
    cn0
    wph
    cP
    cn
    wcel
    @1
    cn0
    wcel
    etransclem22.p
    cP
    nnm1nn0
    syl
    wph
    cP
    etransclem22.p
    nnnn0d
    ifcld
    #
    faccld
    nncnd
    adantr
    @22
    @6
    @22
    @5
    @22
    @5
    cz
    wcel
    #
    cc0
    @5
    cle
    wbr
    #
    @5
    cn0
    wcel
    #
    wph
    @28
    @21
    wph
    @2
    cN
    wph
    @2
    @27
    nn0zd
    wph
    cN
    etransclem22.n
    nn0zd
    zsubcld
    adantr
    @22
    @29
    cN
    @2
    cle
    wbr
    @22
    cN
    @2
    wph
    cN
    cr
    wcel
    @21
    wph
    cN
    etransclem22.n
    nn0red
    adantr
    #
    wph
    @2
    cr
    wcel
    @21
    wph
    @2
    @27
    nn0red
    adantr
    #
    @23
    nltled
    @22
    @2
    cN
    @32
    @31
    subge0d
    mpbird
    @5
    elnn0z
    sylanbrc
    #
    faccld
    #
    nncnd
    @22
    @6
    @34
    nnne0d
    divcld
    @26
    constcncfg
    @22
    @30
    vy
    cc
    @25
    cmpt
    cc
    cc
    ccncf
    co
    wcel
    @33
    vy
    @5
    expcncf
    syl
    mulcncf
    @26
    @24
    @9
    wceq
    @25
    @10
    @7
    cmul
    @24
    @9
    @5
    cexp
    oveq1
    oveq2d
    cncfcompt2
    eqeltrd
    pm2.61dan
    eqeltrd
end
