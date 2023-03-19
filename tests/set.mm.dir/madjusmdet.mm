include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "eqeq1.mm"
include "breq1.mm"
include "oveq1.mm"
include "id.mm"
include "ifbieq12d.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "madjusmdetlem4.mm"

theorem madjusmdet
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cE: class E
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let cP: class P
  let cQ: class Q
  assume madjusmdet.b: |- B = ( Base ` A )
  assume madjusmdet.a: |- A = ( ( 1 ... N ) Mat R )
  assume madjusmdet.d: |- D = ( ( 1 ... N ) maDet R )
  assume madjusmdet.k: |- K = ( ( 1 ... N ) maAdju R )
  assume madjusmdet.t: |- .x. = ( .r ` R )
  assume madjusmdet.z: |- Z = ( ZRHom ` R )
  assume madjusmdet.e: |- E = ( ( 1 ... ( N - 1 ) ) maDet R )
  assume madjusmdet.n: |- ( ph -> N e. NN )
  assume madjusmdet.r: |- ( ph -> R e. CRing )
  assume madjusmdet.i: |- ( ph -> I e. ( 1 ... N ) )
  assume madjusmdet.j: |- ( ph -> J e. ( 1 ... N ) )
  assume madjusmdet.m: |- ( ph -> M e. B )


  assert |- ( ph -> ( J ( K ` M ) I ) = ( ( Z ` ( -u 1 ^ ( I + J ) ) ) .x. ( E ` ( I ( subMat1 ` M ) J ) ) ) )

  proof
    wph
    cA
    cB
    cD
    vk
    c1
    cN
    cfz
    co
    #
    vk
    cv
    #
    c1
    wceq
    #
    cI
    @1
    cI
    cle
    wbr
    #
    @1
    c1
    cmin
    co
    #
    @1
    cif
    #
    cif
    #
    cmpt
    vl
    @0
    vl
    cv
    #
    c1
    wceq
    #
    cJ
    @7
    cJ
    cle
    wbr
    #
    @7
    c1
    cmin
    co
    #
    @7
    cif
    #
    cif
    #
    cmpt
    cR
    vk
    @0
    @2
    cN
    @1
    cN
    cle
    wbr
    #
    @4
    @1
    cif
    #
    cif
    #
    cmpt
    vl
    @0
    @8
    cN
    @7
    cN
    cle
    wbr
    #
    @10
    @7
    cif
    #
    cif
    #
    cmpt
    c.x
    vi
    vj
    cE
    cI
    cJ
    cK
    cM
    cN
    cZ
    madjusmdet.b
    madjusmdet.a
    madjusmdet.d
    madjusmdet.k
    madjusmdet.t
    madjusmdet.z
    madjusmdet.e
    madjusmdet.n
    madjusmdet.r
    madjusmdet.i
    madjusmdet.j
    madjusmdet.m
    vk
    vi
    @0
    @6
    vi
    cv
    #
    c1
    wceq
    #
    cI
    @19
    cI
    cle
    wbr
    #
    @19
    c1
    cmin
    co
    #
    @19
    cif
    #
    cif
    @1
    @19
    wceq
    #
    @2
    @20
    @5
    @23
    cI
    @1
    @19
    c1
    eqeq1
    #
    @24
    @3
    @21
    @4
    @1
    @22
    @19
    @1
    @19
    cI
    cle
    breq1
    @1
    @19
    c1
    cmin
    oveq1
    #
    @24
    id
    #
    ifbieq12d
    ifbieq2d
    cbvmptv
    vk
    vi
    @0
    @15
    @20
    cN
    @19
    cN
    cle
    wbr
    #
    @22
    @19
    cif
    #
    cif
    @24
    @2
    @20
    @14
    @29
    cN
    @25
    @24
    @13
    @28
    @4
    @1
    @22
    @19
    @1
    @19
    cN
    cle
    breq1
    @26
    @27
    ifbieq12d
    ifbieq2d
    cbvmptv
    vl
    vj
    @0
    @12
    vj
    cv
    #
    c1
    wceq
    #
    cJ
    @30
    cJ
    cle
    wbr
    #
    @30
    c1
    cmin
    co
    #
    @30
    cif
    #
    cif
    @7
    @30
    wceq
    #
    @8
    @31
    @11
    @34
    cJ
    @7
    @30
    c1
    eqeq1
    #
    @35
    @9
    @32
    @10
    @7
    @33
    @30
    @7
    @30
    cJ
    cle
    breq1
    @7
    @30
    c1
    cmin
    oveq1
    #
    @35
    id
    #
    ifbieq12d
    ifbieq2d
    cbvmptv
    vl
    vj
    @0
    @18
    @31
    cN
    @30
    cN
    cle
    wbr
    #
    @33
    @30
    cif
    #
    cif
    @35
    @8
    @31
    @17
    @40
    cN
    @36
    @35
    @16
    @39
    @10
    @7
    @33
    @30
    @7
    @30
    cN
    cle
    breq1
    @37
    @38
    ifbieq12d
    ifbieq2d
    cbvmptv
    madjusmdetlem4
end
