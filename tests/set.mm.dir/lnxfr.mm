include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "cs3.mm"
include "wbr.mm"
include "simpr.mm"
include "tgbtwnxfr.mm"
include "btwncolg1.mm"
include "cgr3swap12.mm"
include "btwncolg2.mm"
include "cgr3swap23.mm"
include "btwncolg3.mm"
include "w3o.mm"
include "tgcolg.mm"
include "mpbid.mm"
include "mpjao3dan.mm"

theorem lnxfr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.sm: class .~
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tglngval.p: |- P = ( Base ` G )
  assume tglngval.l: |- L = ( LineG ` G )
  assume tglngval.i: |- I = ( Itv ` G )
  assume tglngval.g: |- ( ph -> G e. TarskiG )
  assume tglngval.x: |- ( ph -> X e. P )
  assume tglngval.y: |- ( ph -> Y e. P )
  assume tgcolg.z: |- ( ph -> Z e. P )
  assume lnxfr.r: |- .~ = ( cgrG ` G )
  assume lnxfr.a: |- ( ph -> A e. P )
  assume lnxfr.b: |- ( ph -> B e. P )
  assume lnxfr.c: |- ( ph -> C e. P )
  assume lnxfr.1: |- ( ph -> ( Y e. ( X L Z ) \/ X = Z ) )
  assume lnxfr.2: |- ( ph -> <" X Y Z "> .~ <" A B C "> )


  assert |- ( ph -> ( B e. ( A L C ) \/ A = C ) )

  proof
    wph
    cY
    cX
    cZ
    cI
    co
    wcel
    #
    cB
    cA
    cC
    cL
    co
    wcel
    cA
    cC
    wceq
    wo
    cX
    cY
    cZ
    cI
    co
    wcel
    #
    cZ
    cX
    cY
    cI
    co
    wcel
    #
    wph
    @0
    wa
    #
    cP
    cG
    cI
    cL
    cA
    cC
    cB
    tglngval.p
    tglngval.l
    tglngval.i
    wph
    cG
    cstrkg
    wcel
    #
    @0
    tglngval.g
    adantr
    #
    wph
    cA
    cP
    wcel
    #
    @0
    lnxfr.a
    adantr
    #
    wph
    cC
    cP
    wcel
    #
    @0
    lnxfr.c
    adantr
    #
    wph
    cB
    cP
    wcel
    #
    @0
    lnxfr.b
    adantr
    #
    @3
    cX
    cY
    cZ
    cA
    cP
    c.sm
    cB
    cC
    cG
    cI
    cG
    cds
    cfv
    #
    tglngval.p
    @12
    eqid
    #
    tglngval.i
    lnxfr.r
    @5
    wph
    cX
    cP
    wcel
    #
    @0
    tglngval.x
    adantr
    wph
    cY
    cP
    wcel
    #
    @0
    tglngval.y
    adantr
    wph
    cZ
    cP
    wcel
    #
    @0
    tgcolg.z
    adantr
    @7
    @11
    @9
    wph
    cX
    cY
    cZ
    cs3
    cA
    cB
    cC
    cs3
    c.sm
    wbr
    #
    @0
    lnxfr.2
    adantr
    wph
    @0
    simpr
    tgbtwnxfr
    btwncolg1
    wph
    @1
    wa
    #
    cP
    cG
    cI
    cL
    cA
    cC
    cB
    tglngval.p
    tglngval.l
    tglngval.i
    wph
    @4
    @1
    tglngval.g
    adantr
    #
    wph
    @6
    @1
    lnxfr.a
    adantr
    #
    wph
    @8
    @1
    lnxfr.c
    adantr
    #
    wph
    @10
    @1
    lnxfr.b
    adantr
    #
    @18
    cY
    cX
    cZ
    cB
    cP
    c.sm
    cA
    cC
    cG
    cI
    @12
    tglngval.p
    @13
    tglngval.i
    lnxfr.r
    @19
    wph
    @15
    @1
    tglngval.y
    adantr
    #
    wph
    @14
    @1
    tglngval.x
    adantr
    #
    wph
    @16
    @1
    tgcolg.z
    adantr
    #
    @22
    @20
    @21
    @18
    cX
    cY
    cZ
    cA
    cP
    c.sm
    cB
    cC
    cG
    cI
    @12
    tglngval.p
    @13
    tglngval.i
    lnxfr.r
    @19
    @24
    @23
    @25
    @20
    @22
    @21
    wph
    @17
    @1
    lnxfr.2
    adantr
    cgr3swap12
    wph
    @1
    simpr
    tgbtwnxfr
    btwncolg2
    wph
    @2
    wa
    #
    cP
    cG
    cI
    cL
    cA
    cC
    cB
    tglngval.p
    tglngval.l
    tglngval.i
    wph
    @4
    @2
    tglngval.g
    adantr
    #
    wph
    @6
    @2
    lnxfr.a
    adantr
    #
    wph
    @8
    @2
    lnxfr.c
    adantr
    #
    wph
    @10
    @2
    lnxfr.b
    adantr
    #
    @26
    cX
    cZ
    cY
    cA
    cP
    c.sm
    cC
    cB
    cG
    cI
    @12
    tglngval.p
    @13
    tglngval.i
    lnxfr.r
    @27
    wph
    @14
    @2
    tglngval.x
    adantr
    #
    wph
    @16
    @2
    tgcolg.z
    adantr
    #
    wph
    @15
    @2
    tglngval.y
    adantr
    #
    @28
    @29
    @30
    @26
    cX
    cY
    cZ
    cA
    cP
    c.sm
    cB
    cC
    cG
    cI
    @12
    tglngval.p
    @13
    tglngval.i
    lnxfr.r
    @27
    @31
    @33
    @32
    @28
    @30
    @29
    wph
    @17
    @2
    lnxfr.2
    adantr
    cgr3swap23
    wph
    @2
    simpr
    tgbtwnxfr
    btwncolg3
    wph
    cY
    cX
    cZ
    cL
    co
    wcel
    cX
    cZ
    wceq
    wo
    @0
    @1
    @2
    w3o
    lnxfr.1
    wph
    cP
    cG
    cI
    cL
    cX
    cZ
    cY
    tglngval.p
    tglngval.l
    tglngval.i
    tglngval.g
    tglngval.x
    tgcolg.z
    tglngval.y
    tgcolg
    mpbid
    mpjao3dan
end
