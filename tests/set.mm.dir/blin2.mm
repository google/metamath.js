include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cin.mm"
include "wa.mm"
include "cbl.mm"
include "crn.mm"
include "cv.mm"
include "co.mm"
include "wss.mm"
include "crp.mm"
include "wrex.mm"
include "simpll.mm"
include "simprl.mm"
include "simplr.mm"
include "elin.mm"
include "sylib.mm"
include "simpld.mm"
include "blss.mm"
include "syl3anc.mm"
include "simprr.mm"
include "simprd.mm"
include "reeanv.mm"
include "ss2in.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cxr.mm"
include "wceq.mm"
include "inss1.mm"
include "cpw.mm"
include "cxp.mm"
include "wf.mm"
include "blf.mm"
include "frn.mm"
include "3syl.mm"
include "sseldd.mm"
include "elpwid.mm"
include "syl5ss.mm"
include "jca.mm"
include "rpxr.mm"
include "anim12i.mm"
include "blin.mm"
include "syl2an.mm"
include "sseq1d.mm"
include "wi.mm"
include "ifcl.mm"
include "oveq2.mm"
include "rspcev.mm"
include "ex.mm"
include "syl.mm"
include "adantl.mm"
include "sylbid.mm"
include "syl5.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "mp2and.mm"

theorem blin2
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cX: class X
  let vr: setvar r
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cR: class R
  let cS: class S

  disjoint B x
  disjoint C x
  disjoint D x
  disjoint P x
  disjoint X x
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint r z
  disjoint B r
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint D r
  disjoint D y
  disjoint D z
  disjoint R r
  disjoint R x
  disjoint P r
  disjoint P y
  disjoint P z
  disjoint S x
  disjoint X r
  disjoint X y
  disjoint X z
  assert |- ( ( ( D e. ( *Met ` X ) /\ P e. ( B i^i C ) ) /\ ( B e. ran ( ball ` D ) /\ C e. ran ( ball ` D ) ) ) -> E. x e. RR+ ( P ( ball ` D ) x ) C_ ( B i^i C ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cB
    cC
    cin
    #
    wcel
    #
    wa
    #
    cB
    cD
    cbl
    cfv
    #
    crn
    #
    wcel
    #
    cC
    @5
    wcel
    #
    wa
    #
    wa
    #
    cP
    vy
    cv
    #
    @4
    co
    #
    cB
    wss
    #
    vy
    crp
    wrex
    #
    cP
    vz
    cv
    #
    @4
    co
    #
    cC
    wss
    #
    vz
    crp
    wrex
    #
    cP
    vx
    cv
    #
    @4
    co
    #
    @1
    wss
    #
    vx
    crp
    wrex
    #
    @9
    @0
    @6
    cP
    cB
    wcel
    #
    @13
    @0
    @2
    @8
    simpll
    #
    @3
    @6
    @7
    simprl
    #
    @9
    @22
    cP
    cC
    wcel
    #
    @9
    @2
    @22
    @25
    wa
    @0
    @2
    @8
    simplr
    #
    cP
    cB
    cC
    elin
    sylib
    #
    simpld
    vy
    cB
    cD
    cP
    cX
    blss
    syl3anc
    @9
    @0
    @7
    @25
    @17
    @23
    @3
    @6
    @7
    simprr
    @9
    @22
    @25
    @27
    simprd
    vz
    cC
    cD
    cP
    cX
    blss
    syl3anc
    @13
    @17
    wa
    @12
    @16
    wa
    #
    vz
    crp
    wrex
    vy
    crp
    wrex
    @9
    @21
    @12
    @16
    vy
    vz
    crp
    crp
    reeanv
    @9
    @28
    @21
    vy
    vz
    crp
    crp
    @28
    @11
    @15
    cin
    #
    @1
    wss
    #
    @9
    @10
    crp
    wcel
    #
    @14
    crp
    wcel
    #
    wa
    #
    wa
    #
    @21
    @11
    cB
    @15
    cC
    ss2in
    @34
    @30
    cP
    @10
    @14
    cle
    wbr
    #
    @10
    @14
    cif
    #
    @4
    co
    #
    @1
    wss
    #
    @21
    @34
    @29
    @37
    @1
    @9
    @0
    cP
    cX
    wcel
    #
    wa
    @10
    cxr
    wcel
    #
    @14
    cxr
    wcel
    #
    wa
    @29
    @37
    wceq
    @33
    @9
    @0
    @39
    @23
    @9
    @1
    cX
    cP
    @9
    @1
    cB
    cX
    cB
    cC
    inss1
    @9
    cB
    cX
    @9
    @5
    cX
    cpw
    #
    cB
    @9
    @0
    cX
    cxr
    cxp
    #
    @42
    @4
    wf
    @5
    @42
    wss
    @23
    cD
    cX
    blf
    @43
    @42
    @4
    frn
    3syl
    @24
    sseldd
    elpwid
    syl5ss
    @26
    sseldd
    jca
    @31
    @40
    @32
    @41
    @10
    rpxr
    @14
    rpxr
    anim12i
    cD
    cP
    @10
    @14
    cX
    blin
    syl2an
    sseq1d
    @33
    @38
    @21
    wi
    #
    @9
    @33
    @36
    crp
    wcel
    #
    @44
    @35
    @10
    @14
    crp
    ifcl
    @45
    @38
    @21
    @20
    @38
    vx
    @36
    crp
    @18
    @36
    wceq
    @19
    @37
    @1
    @18
    @36
    cP
    @4
    oveq2
    sseq1d
    rspcev
    ex
    syl
    adantl
    sylbid
    syl5
    rexlimdvva
    syl5bir
    mp2and
end
