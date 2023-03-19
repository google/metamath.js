include "ccrg.mm"
include "wcel.mm"
include "weq.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "cif.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cmdat.mm"
include "wa.mm"
include "cbs.mm"
include "eqid.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "adantl.mm"
include "simpld.mm"
include "simpl.mm"
include "w3a.mm"
include "wf.mm"
include "mdetf.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "simp1l.mm"
include "crg.mm"
include "simp11l.mm"
include "crngring.mm"
include "ringidcl.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "3syl.mm"
include "simp2.mm"
include "simp3.mm"
include "simp11r.mm"
include "matecld.mm"
include "matbas2d.mm"
include "ffvelrnd.mm"
include "madufval.mm"
include "fmptd.mm"

theorem maduf
  let cA: class A
  let cB: class B
  let cR: class R
  let cJ: class J
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  assume maduf.a: |- A = ( N Mat R )
  assume maduf.j: |- J = ( N maAdju R )
  assume maduf.b: |- B = ( Base ` A )


  assert |- ( R e. CRing -> J : B --> B )

  proof
    cR
    ccrg
    wcel
    #
    vm
    cB
    vi
    vj
    cN
    cN
    vk
    vl
    cN
    cN
    vk
    vj
    weq
    #
    vl
    vi
    weq
    #
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    #
    vk
    cv
    #
    vl
    cv
    #
    vm
    cv
    #
    co
    #
    cif
    #
    cmpt2
    #
    cN
    cR
    cmdat
    co
    #
    cfv
    #
    cmpt2
    cB
    cJ
    @0
    @8
    cB
    wcel
    #
    wa
    #
    vi
    vj
    cA
    cB
    @13
    cR
    cR
    cbs
    cfv
    #
    cN
    ccrg
    maduf.a
    @16
    eqid
    #
    maduf.b
    @15
    cN
    cfn
    wcel
    #
    cR
    cvv
    wcel
    #
    @14
    @18
    @19
    wa
    @0
    cA
    cB
    cR
    cN
    @8
    maduf.a
    maduf.b
    matrcl
    adantl
    simpld
    #
    @0
    @14
    simpl
    @15
    vi
    cv
    cN
    wcel
    #
    vj
    cv
    cN
    wcel
    #
    w3a
    #
    cB
    @16
    @11
    @12
    @15
    @21
    cB
    @16
    @12
    wf
    #
    @22
    @0
    @24
    @14
    cA
    cB
    @12
    cR
    @16
    cN
    @12
    eqid
    #
    maduf.a
    maduf.b
    @17
    mdetf
    adantr
    3ad2ant1
    @23
    vk
    vl
    cA
    cB
    @10
    cR
    @16
    cN
    ccrg
    maduf.a
    @17
    maduf.b
    @15
    @21
    @18
    @22
    @20
    3ad2ant1
    @0
    @14
    @21
    @22
    simp1l
    @23
    @6
    cN
    wcel
    #
    @7
    cN
    wcel
    #
    w3a
    #
    @1
    @5
    @9
    @16
    @28
    @0
    cR
    crg
    wcel
    #
    @5
    @16
    wcel
    @0
    @14
    @21
    @22
    @26
    @27
    simp11l
    cR
    crngring
    @29
    @2
    @3
    @4
    @16
    @16
    cR
    @3
    @17
    @3
    eqid
    #
    ringidcl
    @16
    cR
    @4
    @17
    @4
    eqid
    #
    ring0cl
    ifcld
    3syl
    @28
    cA
    cB
    cR
    @6
    @7
    @16
    @8
    cN
    maduf.a
    @17
    maduf.b
    @23
    @26
    @27
    simp2
    @23
    @26
    @27
    simp3
    @0
    @14
    @21
    @22
    @26
    @27
    simp11r
    matecld
    ifcld
    matbas2d
    ffvelrnd
    matbas2d
    cA
    cB
    @12
    cR
    @3
    vi
    vj
    vk
    vm
    cJ
    cN
    @4
    vl
    maduf.a
    @25
    maduf.j
    maduf.b
    @30
    @31
    madufval
    fmptd
end
