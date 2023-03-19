include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubg.mm"
include "cv.mm"
include "co.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "isnsg.mm"
include "dfbi2.mm"
include "ralbii.mm"
include "r19.26-2.mm"
include "bitri.mm"
include "weq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "oveq1.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "ralcom.mm"
include "ralbidv.mm"
include "3bitri.mm"
include "anbi12i.mm"
include "anidm.mm"
include "anbi2i.mm"

theorem isnsg2
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cS: class S
  let cG: class G
  let cX: class X
  let cA: class A
  let vb: setvar b
  let vg: setvar g
  let vp: setvar p
  let vs: setvar s
  let vz: setvar z
  let cB: class B
  assume isnsg.1: |- X = ( Base ` G )
  assume isnsg.2: |- .+ = ( +g ` G )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint .+ x
  disjoint .+ y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint A x
  disjoint A y
  disjoint b g
  disjoint b p
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint G b
  disjoint g p
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint p s
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint G p
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint x z
  disjoint y z
  disjoint G z
  disjoint .+ b
  disjoint .+ g
  disjoint .+ p
  disjoint .+ s
  disjoint .+ z
  disjoint S s
  disjoint S z
  disjoint B y
  disjoint X b
  disjoint X g
  disjoint X p
  disjoint X s
  disjoint X z
  assert |- ( S e. ( NrmSGrp ` G ) <-> ( S e. ( SubGrp ` G ) /\ A. x e. X A. y e. X ( ( x .+ y ) e. S -> ( y .+ x ) e. S ) ) )

  proof
    cS
    cG
    cnsg
    cfv
    wcel
    cS
    cG
    csubg
    cfv
    wcel
    #
    vx
    cv
    #
    vz
    cv
    #
    c.pl
    co
    #
    cS
    wcel
    #
    @2
    @1
    c.pl
    co
    #
    cS
    wcel
    #
    wb
    #
    vz
    cX
    wral
    #
    vx
    cX
    wral
    #
    wa
    @0
    @1
    vy
    cv
    #
    c.pl
    co
    #
    cS
    wcel
    #
    @10
    @1
    c.pl
    co
    #
    cS
    wcel
    #
    wi
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    wa
    vx
    vz
    c.pl
    cS
    cG
    cX
    isnsg.1
    isnsg.2
    isnsg
    @9
    @17
    @0
    @9
    @4
    @6
    wi
    #
    vz
    cX
    wral
    #
    vx
    cX
    wral
    #
    @6
    @4
    wi
    #
    vz
    cX
    wral
    vx
    cX
    wral
    #
    wa
    #
    @17
    @17
    wa
    @17
    @9
    @18
    @21
    wa
    #
    vz
    cX
    wral
    #
    vx
    cX
    wral
    @23
    @8
    @25
    vx
    cX
    @7
    @24
    vz
    cX
    @4
    @6
    dfbi2
    ralbii
    ralbii
    @18
    @21
    vx
    vz
    cX
    cX
    r19.26-2
    bitri
    @20
    @17
    @22
    @17
    @19
    @16
    vx
    cX
    @18
    @15
    vz
    vy
    cX
    vz
    vy
    weq
    #
    @4
    @12
    @6
    @14
    @26
    @3
    @11
    cS
    @2
    @10
    @1
    c.pl
    oveq2
    eleq1d
    @26
    @5
    @13
    cS
    @2
    @10
    @1
    c.pl
    oveq1
    eleq1d
    imbi12d
    cbvralv
    ralbii
    @22
    @21
    vx
    cX
    wral
    #
    vz
    cX
    wral
    @2
    @10
    c.pl
    co
    #
    cS
    wcel
    #
    @10
    @2
    c.pl
    co
    #
    cS
    wcel
    #
    wi
    #
    vy
    cX
    wral
    #
    vz
    cX
    wral
    @17
    @21
    vx
    vz
    cX
    cX
    ralcom
    @27
    @33
    vz
    cX
    @21
    @32
    vx
    vy
    cX
    vx
    vy
    weq
    #
    @6
    @29
    @4
    @31
    @34
    @5
    @28
    cS
    @1
    @10
    @2
    c.pl
    oveq2
    eleq1d
    @34
    @3
    @30
    cS
    @1
    @10
    @2
    c.pl
    oveq1
    eleq1d
    imbi12d
    cbvralv
    ralbii
    @33
    @16
    vz
    vx
    cX
    vz
    vx
    weq
    #
    @32
    @15
    vy
    cX
    @35
    @29
    @12
    @31
    @14
    @35
    @28
    @11
    cS
    @2
    @1
    @10
    c.pl
    oveq1
    eleq1d
    @35
    @30
    @13
    cS
    @2
    @1
    @10
    c.pl
    oveq2
    eleq1d
    imbi12d
    ralbidv
    cbvralv
    3bitri
    anbi12i
    @17
    anidm
    3bitri
    anbi2i
    bitri
end
