include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cvsca.mm"
include "cfv.mm"
include "clinc.mm"
include "wceq.mm"
include "cplusg.mm"
include "cres.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2.mm"
include "3ad2ant2.mm"
include "lincext1.mm"
include "3adant3.mm"
include "lincext2.mm"
include "3adant3r.mm"
include "wf.mm"
include "elmapi.mm"
include "fdmdifeqresdif.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "eqid.mm"
include "lincdifsn.mm"
include "syl321anc.mm"
include "oveq1.mm"
include "eqcoms.mm"
include "adantl.mm"
include "cminusg.mm"
include "simpll.mm"
include "wi.mm"
include "elelpwi.mm"
include "expcom.mm"
include "com12.mm"
include "impcom.mm"
include "simpr1.mm"
include "lmodvsneg.mm"
include "cv.mm"
include "cif.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "iftrue.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "oveq2d.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "lmodvnegid.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem lincext3
  let vz: setvar z
  let cB: class B
  let cR: class R
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume lincext.b: |- B = ( Base ` M )
  assume lincext.r: |- R = ( Scalar ` M )
  assume lincext.e: |- E = ( Base ` R )
  assume lincext.0: |- .0. = ( 0g ` R )
  assume lincext.z: |- Z = ( 0g ` M )
  assume lincext.n: |- N = ( invg ` R )
  assume lincext.f: |- F = ( z e. S |-> if ( z = X , ( N ` Y ) , ( G ` z ) ) )

  disjoint B z
  disjoint E z
  disjoint G z
  disjoint M z
  disjoint S z
  disjoint X z
  disjoint Y z
  disjoint N z
  disjoint k x
  assert |- ( ( ( M e. LMod /\ S e. ~P B ) /\ ( Y e. E /\ X e. S /\ G e. ( E ^m ( S \ { X } ) ) ) /\ ( G finSupp .0. /\ ( Y ( .s ` M ) X ) = ( G ( linC ` M ) ( S \ { X } ) ) ) ) -> ( F ( linC ` M ) S ) = Z )

  proof
    cM
    clmod
    wcel
    #
    cS
    cB
    cpw
    wcel
    #
    wa
    #
    cY
    cE
    wcel
    #
    cX
    cS
    wcel
    #
    cG
    cE
    cS
    cX
    csn
    cdif
    #
    cmap
    co
    wcel
    #
    w3a
    #
    cG
    c.0
    cfsupp
    wbr
    #
    cY
    cX
    cM
    cvsca
    cfv
    #
    co
    #
    cG
    @5
    cM
    clinc
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    w3a
    #
    cF
    cS
    @11
    co
    #
    @12
    cX
    cF
    cfv
    #
    cX
    @9
    co
    #
    cM
    cplusg
    cfv
    #
    co
    #
    cZ
    @15
    @0
    @1
    @4
    cF
    cE
    cS
    cmap
    co
    wcel
    #
    cF
    c.0
    cfsupp
    wbr
    #
    cG
    cF
    @5
    cres
    wceq
    #
    @16
    @20
    wceq
    @0
    @1
    @7
    @14
    simp1l
    @0
    @1
    @7
    @14
    simp1r
    @7
    @2
    @4
    @14
    @3
    @4
    @6
    simp2
    #
    3ad2ant2
    @2
    @7
    @21
    @14
    vz
    cB
    cR
    cS
    cE
    cF
    cG
    cM
    cN
    cX
    cY
    c.0
    cZ
    lincext.b
    lincext.r
    lincext.e
    lincext.0
    lincext.z
    lincext.n
    lincext.f
    lincext1
    3adant3
    @2
    @7
    @8
    @22
    @13
    vz
    cB
    cR
    cS
    cE
    cF
    cG
    cM
    cN
    cX
    cY
    c.0
    cZ
    lincext.b
    lincext.r
    lincext.e
    lincext.0
    lincext.z
    lincext.n
    lincext.f
    lincext2
    3adant3r
    @7
    @2
    @23
    @14
    @6
    @3
    @23
    @4
    @6
    @5
    cE
    cG
    wf
    @23
    cG
    cE
    @5
    elmapi
    vz
    cS
    cE
    cF
    cG
    cY
    cN
    cfv
    #
    cX
    lincext.f
    fdmdifeqresdif
    syl
    3ad2ant3
    3ad2ant2
    cB
    @19
    cR
    cE
    @9
    cF
    cG
    cM
    cS
    cX
    c.0
    lincext.b
    lincext.r
    lincext.e
    @9
    eqid
    #
    @19
    eqid
    #
    lincext.0
    lincdifsn
    syl321anc
    @15
    @20
    @10
    @18
    @19
    co
    #
    cZ
    @14
    @2
    @20
    @28
    wceq
    #
    @7
    @13
    @29
    @8
    @29
    @12
    @10
    @12
    @10
    @18
    @19
    oveq1
    eqcoms
    adantl
    3ad2ant3
    @2
    @7
    @28
    cZ
    wceq
    @14
    @2
    @7
    wa
    #
    @28
    @10
    @10
    cM
    cminusg
    cfv
    #
    cfv
    #
    @19
    co
    #
    cZ
    @30
    @18
    @32
    @10
    @19
    @30
    @32
    @25
    cX
    @9
    co
    @18
    @30
    cB
    cY
    @9
    cR
    cE
    cN
    @31
    cM
    cX
    lincext.b
    lincext.r
    @26
    @31
    eqid
    #
    lincext.e
    lincext.n
    @0
    @1
    @7
    simpll
    #
    @7
    @2
    cX
    cB
    wcel
    #
    @4
    @3
    @2
    @36
    wi
    @6
    @2
    @4
    @36
    @1
    @4
    @36
    wi
    @0
    @4
    @1
    @36
    cX
    cS
    cB
    elelpwi
    expcom
    adantl
    com12
    3ad2ant2
    impcom
    #
    @2
    @3
    @4
    @6
    simpr1
    #
    lmodvsneg
    @30
    @25
    @17
    cX
    @9
    @30
    @17
    @25
    @30
    vz
    cX
    vz
    cv
    #
    cX
    wceq
    #
    @25
    @39
    cG
    cfv
    #
    cif
    #
    @25
    cS
    cF
    cvv
    cF
    vz
    cS
    @42
    cmpt
    wceq
    @30
    lincext.f
    a1i
    @40
    @42
    @25
    wceq
    @30
    @40
    @25
    @41
    iftrue
    adantl
    @7
    @4
    @2
    @24
    adantl
    @30
    cY
    cN
    fvexd
    fvmptd
    eqcomd
    oveq1d
    eqtr2d
    oveq2d
    @30
    @0
    @10
    cB
    wcel
    #
    @33
    cZ
    wceq
    @35
    @30
    @0
    @3
    @36
    @43
    @35
    @38
    @37
    cY
    @9
    cR
    cE
    cB
    cM
    cX
    lincext.b
    lincext.r
    @26
    lincext.e
    lmodvscl
    syl3anc
    @19
    @31
    cB
    cM
    @10
    cZ
    lincext.b
    @27
    lincext.z
    @34
    lmodvnegid
    syl2anc
    eqtrd
    3adant3
    eqtrd
    eqtrd
end
