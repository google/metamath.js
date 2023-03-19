include "cc.mm"
include "cfv.mm"
include "cdvn.mm"
include "co.mm"
include "wf.mm"
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
include "wcel.mm"
include "wa.mm"
include "iftrue.mm"
include "0cnd.mm"
include "eqeltrd.mm"
include "adantl.mm"
include "wn.mm"
include "simpr.mm"
include "iffalsed.mm"
include "cn0.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nnnn0d.mm"
include "ifcld.mm"
include "faccld.mm"
include "nncnd.mm"
include "adantr.mm"
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
include "adantlr.mm"
include "dvdmsscn.mm"
include "sselda.mm"
include "cfz.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "subcld.mm"
include "expcld.mm"
include "mulcld.mm"
include "pm2.61dan.mm"
include "eqid.mm"
include "fmptd.mm"
include "etransclem17.mm"
include "feq1d.mm"

theorem etransclem20
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
  let vk: setvar k
  assume etransclem20.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem20.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem20.p: |- ( ph -> P e. NN )
  assume etransclem20.h: |- H = ( j e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) )
  assume etransclem20.J: |- ( ph -> J e. ( 0 ... M ) )
  assume etransclem20.n: |- ( ph -> N e. NN0 )

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
  disjoint k x
  assert |- ( ph -> ( ( S Dn ( H ` J ) ) ` N ) : X --> CC )

  proof
    wph
    cX
    cc
    cN
    cS
    cJ
    cH
    cfv
    cdvn
    co
    cfv
    #
    wf
    cX
    cc
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
    @3
    cfa
    cfv
    #
    @3
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
    @6
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
    wf
    wph
    vx
    cX
    @13
    cc
    @14
    wph
    @9
    cX
    wcel
    #
    wa
    #
    @4
    @13
    cc
    wcel
    #
    @4
    @17
    @16
    @4
    @13
    cc0
    cc
    @4
    cc0
    @12
    iftrue
    @4
    0cnd
    eqeltrd
    adantl
    @16
    @4
    wn
    #
    wa
    #
    @13
    @12
    cc
    @19
    @4
    cc0
    @12
    @16
    @18
    simpr
    iffalsed
    @19
    @8
    @11
    wph
    @18
    @8
    cc
    wcel
    @15
    wph
    @18
    wa
    #
    @5
    @7
    wph
    @5
    cc
    wcel
    @18
    wph
    @5
    wph
    @3
    wph
    @1
    @2
    cP
    cn0
    wph
    cP
    cn
    wcel
    @2
    cn0
    wcel
    etransclem20.p
    cP
    nnm1nn0
    syl
    wph
    cP
    etransclem20.p
    nnnn0d
    ifcld
    #
    faccld
    nncnd
    adantr
    @20
    @7
    @20
    @6
    @20
    @6
    cz
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @6
    cn0
    wcel
    #
    wph
    @22
    @18
    wph
    @3
    cN
    wph
    @3
    @21
    nn0zd
    wph
    cN
    etransclem20.n
    nn0zd
    zsubcld
    adantr
    @20
    @23
    cN
    @3
    cle
    wbr
    @20
    cN
    @3
    wph
    cN
    cr
    wcel
    @18
    wph
    cN
    etransclem20.n
    nn0red
    adantr
    #
    wph
    @3
    cr
    wcel
    @18
    wph
    @3
    @21
    nn0red
    adantr
    #
    wph
    @18
    simpr
    nltled
    @20
    @3
    cN
    @26
    @25
    subge0d
    mpbird
    @6
    elnn0z
    sylanbrc
    #
    faccld
    #
    nncnd
    @20
    @7
    @28
    nnne0d
    divcld
    adantlr
    @19
    @10
    @6
    @16
    @10
    cc
    wcel
    @18
    @16
    @9
    cJ
    wph
    cX
    cc
    @9
    wph
    cS
    cX
    etransclem20.s
    etransclem20.x
    dvdmsscn
    sselda
    wph
    cJ
    cc
    wcel
    #
    @15
    wph
    cJ
    cc0
    cM
    cfz
    co
    wcel
    #
    @29
    etransclem20.J
    @30
    cJ
    cJ
    cc0
    cM
    elfzelz
    zcnd
    syl
    adantr
    subcld
    adantr
    wph
    @18
    @24
    @15
    @27
    adantlr
    expcld
    mulcld
    eqeltrd
    pm2.61dan
    @14
    eqid
    fmptd
    wph
    cX
    cc
    @0
    @14
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
    etransclem20.s
    etransclem20.x
    etransclem20.p
    etransclem20.h
    etransclem20.J
    etransclem20.n
    etransclem17
    feq1d
    mpbird
end
