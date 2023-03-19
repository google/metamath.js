include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cmul.mm"
include "cdiv.mm"
include "csu.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "wral.mm"
include "cn.mm"
include "crp.mm"
include "wrex.mm"
include "clt.mm"
include "wa.mm"
include "cpnf.mm"
include "cioo.mm"
include "ce.mm"
include "cico.mm"
include "cc0.mm"
include "pntrsumbnd2.mm"
include "wcel.mm"
include "c2.mm"
include "simpl.mm"
include "2rp.mm"
include "rpaddcl.mm"
include "sylancl.mm"
include "cr.mm"
include "2re.mm"
include "elioore.mm"
include "adantl.mm"
include "eliooord.mm"
include "simpld.mm"
include "elrpd.mm"
include "rerpdivcl.mm"
include "sylancr.mm"
include "rpefcld.mm"
include "wi.mm"
include "wn.mm"
include "simpllr.mm"
include "eqid.mm"
include "simplrr.mm"
include "simp-4l.mm"
include "simp-4r.mm"
include "simplrl.mm"
include "simpr.mm"
include "pntpbnd2.mm"
include "iman.mm"
include "mpbir.mm"
include "ralrimivva.mm"
include "wceq.mm"
include "oveq1.mm"
include "raleqdv.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "rexbidv.mm"
include "rexlimiva.mm"
include "ax-mp.mm"

theorem pntpbnd
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let ve: setvar e
  let vk: setvar k
  let vn: setvar n
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cE: class E
  let cL: class L
  let cN: class N
  let cA: class A
  let cC: class C
  let cK: class K
  let cM: class M
  let cT: class T
  let cY: class Y
  let cZ: class Z
  let wph: wff ph
  assume pntibnd.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )

  disjoint a k
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint c e
  disjoint c k
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint R c
  disjoint e k
  disjoint e n
  disjoint e x
  disjoint e y
  disjoint R e
  disjoint R k
  disjoint R n
  disjoint R x
  disjoint R y
  disjoint a d
  disjoint a i
  disjoint a j
  disjoint a m
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a z
  disjoint E a
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint E d
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint E i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint E j
  disjoint k m
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k z
  disjoint E k
  disjoint m n
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint E m
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n z
  disjoint E n
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint E t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint E u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint E v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint E w
  disjoint x z
  disjoint E x
  disjoint y z
  disjoint E y
  disjoint E z
  disjoint L n
  disjoint L t
  disjoint L u
  disjoint L v
  disjoint L x
  disjoint L z
  disjoint N a
  disjoint N u
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint C n
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint c d
  disjoint c i
  disjoint c j
  disjoint c m
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c z
  disjoint d e
  disjoint R d
  disjoint e i
  disjoint e j
  disjoint e m
  disjoint e t
  disjoint e u
  disjoint e v
  disjoint e w
  disjoint e z
  disjoint R i
  disjoint R j
  disjoint R m
  disjoint R t
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R z
  disjoint K m
  disjoint M z
  disjoint T x
  disjoint T y
  disjoint Y z
  disjoint Z k
  disjoint Z m
  disjoint Z n
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z x
  disjoint Z y
  disjoint k ph
  disjoint n ph
  disjoint ph t
  disjoint ph u
  disjoint ph w
  assert |- E. c e. RR+ A. e e. ( 0 (,) 1 ) E. x e. RR+ A. k e. ( ( exp ` ( c / e ) ) [,) +oo ) A. y e. ( x (,) +oo ) E. n e. NN ( ( y < n /\ n <_ ( k x. y ) ) /\ ( abs ` ( ( R ` n ) / n ) ) <_ e )

  proof
    vi
    cv
    vj
    cv
    cfz
    co
    vn
    cv
    #
    cR
    cfv
    #
    @0
    @0
    c1
    caddc
    co
    cmul
    co
    cdiv
    co
    vn
    csu
    cabs
    cfv
    vd
    cv
    #
    cle
    wbr
    vj
    cz
    wral
    vi
    cn
    wral
    #
    vd
    crp
    wrex
    vy
    cv
    #
    @0
    clt
    wbr
    @0
    vk
    cv
    #
    @4
    cmul
    co
    cle
    wbr
    wa
    @1
    @0
    cdiv
    co
    cabs
    cfv
    ve
    cv
    #
    cle
    wbr
    wa
    vn
    cn
    wrex
    #
    vy
    vx
    cv
    #
    cpnf
    cioo
    co
    #
    wral
    #
    vk
    vc
    cv
    #
    @6
    cdiv
    co
    #
    ce
    cfv
    #
    cpnf
    cico
    co
    #
    wral
    #
    vx
    crp
    wrex
    #
    ve
    cc0
    c1
    cioo
    co
    #
    wral
    #
    vc
    crp
    wrex
    #
    cR
    vi
    vj
    vn
    va
    vd
    pntibnd.r
    pntrsumbnd2
    @3
    @19
    vd
    crp
    @2
    crp
    wcel
    #
    @3
    wa
    #
    @2
    c2
    caddc
    co
    #
    crp
    wcel
    #
    @10
    vk
    @22
    @6
    cdiv
    co
    #
    ce
    cfv
    #
    cpnf
    cico
    co
    #
    wral
    #
    vx
    crp
    wrex
    #
    ve
    @17
    wral
    #
    @19
    @21
    @20
    c2
    crp
    wcel
    @23
    @20
    @3
    simpl
    2rp
    @2
    c2
    rpaddcl
    sylancl
    @21
    @28
    ve
    @17
    @21
    @6
    @17
    wcel
    #
    wa
    #
    c2
    @6
    cdiv
    co
    #
    ce
    cfv
    #
    crp
    wcel
    @7
    vy
    @33
    cpnf
    cioo
    co
    #
    wral
    #
    vk
    @26
    wral
    #
    @28
    @31
    @32
    @31
    c2
    cr
    wcel
    @6
    crp
    wcel
    @32
    cr
    wcel
    2re
    @31
    @6
    @30
    @6
    cr
    wcel
    @21
    @6
    cc0
    c1
    elioore
    adantl
    @31
    cc0
    @6
    clt
    wbr
    #
    @6
    c1
    clt
    wbr
    #
    @30
    @37
    @38
    wa
    @21
    @6
    cc0
    c1
    eliooord
    adantl
    simpld
    elrpd
    c2
    @6
    rerpdivcl
    sylancr
    rpefcld
    @31
    @7
    vk
    vy
    @26
    @34
    @31
    @5
    @26
    wcel
    #
    @4
    @34
    wcel
    #
    wa
    #
    wa
    #
    @7
    wi
    @42
    @7
    wn
    #
    wa
    #
    wn
    @44
    vn
    @2
    @22
    cR
    vi
    vj
    @6
    @5
    @33
    @4
    va
    pntibnd.r
    @21
    @30
    @41
    @43
    simpllr
    @33
    eqid
    @31
    @39
    @40
    @43
    simplrr
    @20
    @3
    @30
    @41
    @43
    simp-4l
    @20
    @3
    @30
    @41
    @43
    simp-4r
    @22
    eqid
    @31
    @39
    @40
    @43
    simplrl
    @42
    @43
    simpr
    pntpbnd2
    @42
    @7
    iman
    mpbir
    ralrimivva
    @27
    @36
    vx
    @33
    crp
    @8
    @33
    wceq
    #
    @10
    @35
    vk
    @26
    @45
    @7
    vy
    @9
    @34
    @8
    @33
    cpnf
    cioo
    oveq1
    raleqdv
    ralbidv
    rspcev
    syl2anc
    ralrimiva
    @18
    @29
    vc
    @22
    crp
    @11
    @22
    wceq
    #
    @16
    @28
    ve
    @17
    @46
    @15
    @27
    vx
    crp
    @46
    @10
    vk
    @14
    @26
    @46
    @13
    @25
    cpnf
    cico
    @46
    @12
    @24
    ce
    @11
    @22
    @6
    cdiv
    oveq1
    fveq2d
    oveq1d
    raleqdv
    rexbidv
    ralbidv
    rspcev
    syl2anc
    rexlimiva
    ax-mp
end
