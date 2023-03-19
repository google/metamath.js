include "crp.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cioo.mm"
include "co.mm"
include "cr.mm"
include "ioossre.mm"
include "sseldi.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "eliooord.mm"
include "syl.mm"
include "simpld.mm"
include "elrpd.mm"
include "caddc.mm"
include "1rp.mm"
include "rpaddcl.mm"
include "sylancl.mm"
include "syl5eqel.mm"
include "cdiv.mm"
include "cmin.mm"
include "c3.mm"
include "c2.mm"
include "cdc.mm"
include "cmul.mm"
include "cexp.mm"
include "1re.mm"
include "ltaddrp.mm"
include "sylancr.mm"
include "cc.mm"
include "wceq.mm"
include "rpcnd.mm"
include "ax-1cn.mm"
include "addcom.mm"
include "syl5eq.mm"
include "breqtrrd.mm"
include "recgt1d.mm"
include "mpbid.mm"
include "wb.mm"
include "rprecred.mm"
include "difrp.mm"
include "cn.mm"
include "3nn0.mm"
include "2nn.mm"
include "decnncl.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "rpmulcl.mm"
include "rpdivcld.mm"
include "cz.mm"
include "2z.mm"
include "rpexpcl.mm"
include "rpmulcld.mm"
include "3jca.mm"

theorem pntlemd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cF: class F
  let cL: class L
  let va: setvar a
  let vx: setvar x
  let vz: setvar z
  let cC: class C
  let vw: setvar w
  let cI: class I
  let vn: setvar n
  let vy: setvar y
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vu: setvar u
  let cK: class K
  let cM: class M
  let cO: class O
  let vv: setvar v
  let cN: class N
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vl: setvar l
  let cV: class V
  let cU: class U
  let cW: class W
  let cX: class X
  let cY: class Y
  let cE: class E
  let cZ: class Z
  assume pntlem1.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )
  assume pntlem1.a: |- ( ph -> A e. RR+ )
  assume pntlem1.b: |- ( ph -> B e. RR+ )
  assume pntlem1.l: |- ( ph -> L e. ( 0 (,) 1 ) )
  assume pntlem1.d: |- D = ( A + 1 )
  assume pntlem1.f: |- F = ( ( 1 - ( 1 / D ) ) x. ( ( L / ( ; 3 2 x. B ) ) / ( D ^ 2 ) ) )


  assert |- ( ph -> ( L e. RR+ /\ D e. RR+ /\ F e. RR+ ) )

  proof
    wph
    cL
    crp
    wcel
    cD
    crp
    wcel
    #
    cF
    crp
    wcel
    wph
    cL
    wph
    cc0
    c1
    cioo
    co
    #
    cr
    cL
    cc0
    c1
    ioossre
    pntlem1.l
    sseldi
    wph
    cc0
    cL
    clt
    wbr
    #
    cL
    c1
    clt
    wbr
    #
    wph
    cL
    @1
    wcel
    @2
    @3
    wa
    pntlem1.l
    cL
    cc0
    c1
    eliooord
    syl
    simpld
    elrpd
    #
    wph
    cD
    cA
    c1
    caddc
    co
    #
    crp
    pntlem1.d
    wph
    cA
    crp
    wcel
    #
    c1
    crp
    wcel
    @5
    crp
    wcel
    pntlem1.a
    1rp
    cA
    c1
    rpaddcl
    sylancl
    syl5eqel
    #
    wph
    cF
    c1
    c1
    cD
    cdiv
    co
    #
    cmin
    co
    #
    cL
    c3
    c2
    cdc
    #
    cB
    cmul
    co
    #
    cdiv
    co
    #
    cD
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cmul
    co
    crp
    pntlem1.f
    wph
    @9
    @14
    wph
    @8
    c1
    clt
    wbr
    #
    @9
    crp
    wcel
    #
    wph
    c1
    cD
    clt
    wbr
    @15
    wph
    c1
    c1
    cA
    caddc
    co
    #
    cD
    clt
    wph
    c1
    cr
    wcel
    #
    @6
    c1
    @17
    clt
    wbr
    1re
    pntlem1.a
    c1
    cA
    ltaddrp
    sylancr
    wph
    cD
    @5
    @17
    pntlem1.d
    wph
    cA
    cc
    wcel
    c1
    cc
    wcel
    @5
    @17
    wceq
    wph
    cA
    pntlem1.a
    rpcnd
    ax-1cn
    cA
    c1
    addcom
    sylancl
    syl5eq
    breqtrrd
    wph
    cD
    @7
    recgt1d
    mpbid
    wph
    @8
    cr
    wcel
    @18
    @15
    @16
    wb
    wph
    cD
    @7
    rprecred
    1re
    @8
    c1
    difrp
    sylancl
    mpbid
    wph
    @12
    @13
    wph
    cL
    @11
    @4
    wph
    @10
    crp
    wcel
    #
    cB
    crp
    wcel
    @11
    crp
    wcel
    @10
    cn
    wcel
    @19
    c3
    c2
    3nn0
    2nn
    decnncl
    @10
    nnrp
    ax-mp
    pntlem1.b
    @10
    cB
    rpmulcl
    sylancr
    rpdivcld
    wph
    @0
    c2
    cz
    wcel
    @13
    crp
    wcel
    @7
    2z
    cD
    c2
    rpexpcl
    sylancl
    rpdivcld
    rpmulcld
    syl5eqel
    3jca
end
