include "cprime.mm"
include "cin.mm"
include "cn.mm"
include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "wn.mm"
include "cen.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "nnex.mm"
include "inss1.mm"
include "cv.mm"
include "prmnn.mm"
include "ssriv.mm"
include "sstri.mm"
include "ssdomg.mm"
include "mp2.mm"
include "a1i.mm"
include "cfn.mm"
include "crp.mm"
include "clog.mm"
include "cfv.mm"
include "cmpt.mm"
include "co1.mm"
include "logno1.mm"
include "wa.mm"
include "cphi.mm"
include "c1.mm"
include "cfl.mm"
include "cfz.mm"
include "co.mm"
include "cdiv.mm"
include "csu.mm"
include "cmul.mm"
include "cr.mm"
include "adantr.mm"
include "phicld.mm"
include "nnred.mm"
include "simpr.mm"
include "inss2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "sseli.mm"
include "sseldi.mm"
include "nnrpd.mm"
include "relogcl.mm"
include "syl.mm"
include "nndivred.mm"
include "sylan2.mm"
include "fsumrecl.mm"
include "cc.mm"
include "rpssre.mm"
include "recnd.mm"
include "o1const.mm"
include "sylancr.mm"
include "clo1.mm"
include "1red.mm"
include "cle.mm"
include "cc0.mm"
include "log1.mm"
include "nnge1d.mm"
include "wb.mm"
include "1rp.mm"
include "logleb.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "divge0d.mm"
include "fsumless.mm"
include "ello1d.mm"
include "0red.mm"
include "fsumge0.mm"
include "o1lo12.mm"
include "mpbird.mm"
include "o1mul2.mm"
include "remulcld.mm"
include "adantl.mm"
include "cmin.mm"
include "rplogsum.mm"
include "o1dif.mm"
include "ex.mm"
include "mtoi.mm"
include "com.mm"
include "nnenom.mm"
include "sdomentr.mm"
include "mpan2.mm"
include "isfinite2.mm"
include "nsyl.mm"
include "bren2.mm"
include "sylanbrc.mm"

theorem dirith2
  let wph: wff ph
  let cA: class A
  let cT: class T
  let cU: class U
  let cL: class L
  let cN: class N
  let cZ: class Z
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vc: setvar c
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vp: setvar p
  let vt: setvar t
  let c.1: class .1.
  let vd: setvar d
  let cC: class C
  let ve: setvar e
  let vr: setvar r
  let cF: class F
  let cI: class I
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vq: setvar q
  let vv: setvar v
  let cE: class E
  let cK: class K
  let cG: class G
  let cP: class P
  let wps: wff ps
  let cR: class R
  let cS: class S
  let cB: class B
  let cW: class W
  let cD: class D
  let cM: class M
  let cX: class X
  assume rpvmasum.z: |- Z = ( Z/nZ ` N )
  assume rpvmasum.l: |- L = ( ZRHom ` Z )
  assume rpvmasum.a: |- ( ph -> N e. NN )
  assume rpvmasum.u: |- U = ( Unit ` Z )
  assume rpvmasum.b: |- ( ph -> A e. U )
  assume rpvmasum.t: |- T = ( `' L " { A } )


  assert |- ( ph -> ( Prime i^i T ) ~~ NN )

  proof
    wph
    cprime
    cT
    cin
    #
    cn
    cdom
    wbr
    #
    @0
    cn
    csdm
    wbr
    #
    wn
    @0
    cn
    cen
    wbr
    @1
    wph
    cn
    cvv
    wcel
    @0
    cn
    wss
    @1
    nnex
    @0
    cprime
    cn
    cprime
    cT
    inss1
    vp
    cprime
    cn
    vp
    cv
    prmnn
    ssriv
    sstri
    #
    @0
    cn
    cvv
    ssdomg
    mp2
    a1i
    wph
    @0
    cfn
    wcel
    #
    @2
    wph
    @4
    vx
    crp
    vx
    cv
    #
    clog
    cfv
    #
    cmpt
    co1
    wcel
    #
    vx
    logno1
    wph
    @4
    @7
    wph
    @4
    wa
    #
    vx
    crp
    cN
    cphi
    cfv
    #
    c1
    @5
    cfl
    cfv
    cfz
    co
    #
    @0
    cin
    #
    vn
    cv
    #
    clog
    cfv
    #
    @12
    cdiv
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    cmpt
    co1
    wcel
    @7
    @8
    vx
    crp
    @9
    @15
    cr
    @8
    @9
    cr
    wcel
    @5
    crp
    wcel
    #
    @8
    @9
    @8
    cN
    wph
    cN
    cn
    wcel
    @4
    rpvmasum.a
    adantr
    phicld
    nnred
    #
    adantr
    @8
    @15
    cr
    wcel
    @17
    @8
    @11
    @14
    vn
    @8
    @4
    @11
    @0
    wss
    #
    @11
    cfn
    wcel
    wph
    @4
    simpr
    #
    @10
    @0
    inss2
    #
    @0
    @11
    ssfi
    sylancl
    #
    @12
    @11
    wcel
    #
    @8
    @12
    @0
    wcel
    #
    @14
    cr
    wcel
    @11
    @0
    @12
    @21
    sseli
    #
    @8
    @24
    wa
    #
    @13
    @12
    @26
    @12
    crp
    wcel
    #
    @13
    cr
    wcel
    @26
    @12
    @26
    @0
    cn
    @12
    @3
    @8
    @24
    simpr
    sseldi
    #
    nnrpd
    #
    @12
    relogcl
    syl
    #
    @28
    nndivred
    #
    sylan2
    #
    fsumrecl
    #
    adantr
    #
    @8
    crp
    cr
    wss
    #
    @9
    cc
    wcel
    vx
    crp
    @9
    cmpt
    co1
    wcel
    rpssre
    @8
    @9
    @18
    recnd
    vx
    crp
    @9
    o1const
    sylancr
    @8
    vx
    crp
    @15
    cmpt
    #
    co1
    wcel
    @36
    clo1
    wcel
    @8
    vx
    crp
    @15
    c1
    @0
    @14
    vn
    csu
    #
    @35
    @8
    rpssre
    a1i
    @34
    @8
    1red
    @8
    @0
    @14
    vn
    @20
    @31
    fsumrecl
    @8
    @15
    @37
    cle
    wbr
    @17
    c1
    @5
    cle
    wbr
    wa
    @8
    @0
    @14
    @11
    vn
    @20
    @31
    @26
    @13
    @12
    @30
    @29
    @26
    cc0
    c1
    clog
    cfv
    #
    @13
    cle
    log1
    @26
    c1
    @12
    cle
    wbr
    #
    @38
    @13
    cle
    wbr
    #
    @26
    @12
    @28
    nnge1d
    @26
    c1
    crp
    wcel
    @27
    @39
    @40
    wb
    1rp
    @29
    c1
    @12
    logleb
    sylancr
    mpbid
    syl5eqbrr
    divge0d
    #
    @19
    @8
    @21
    a1i
    fsumless
    adantr
    ello1d
    @8
    vx
    crp
    @15
    cc0
    @34
    @8
    0red
    @8
    cc0
    @15
    cle
    wbr
    @17
    @8
    @11
    @14
    vn
    @22
    @32
    @23
    @8
    @24
    cc0
    @14
    cle
    wbr
    @25
    @41
    sylan2
    fsumge0
    adantr
    o1lo12
    mpbird
    o1mul2
    @8
    vx
    crp
    @16
    @6
    @8
    @16
    cc
    wcel
    @17
    @8
    @16
    @8
    @9
    @15
    @18
    @33
    remulcld
    recnd
    adantr
    @8
    @17
    wa
    @6
    @17
    @6
    cr
    wcel
    @8
    @5
    relogcl
    adantl
    recnd
    wph
    vx
    crp
    @16
    @6
    cmin
    co
    cmpt
    co1
    wcel
    @4
    wph
    vx
    cA
    cT
    cU
    cL
    cN
    cZ
    vn
    rpvmasum.z
    rpvmasum.l
    rpvmasum.a
    rpvmasum.u
    rpvmasum.b
    rpvmasum.t
    rplogsum
    adantr
    o1dif
    mpbid
    ex
    mtoi
    @2
    @0
    com
    csdm
    wbr
    #
    @4
    @2
    cn
    com
    cen
    wbr
    @42
    nnenom
    @0
    cn
    com
    sdomentr
    mpan2
    @0
    isfinite2
    syl
    nsyl
    @0
    cn
    bren2
    sylanbrc
end
