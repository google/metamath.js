include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "cfv.mm"
include "cin.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "dihmeetlem8N.mm"
include "syl312anc.mm"
include "ineq1d.mm"
include "dihmeetlem11N.mm"
include "3adantr3.mm"
include "simpr1l.mm"
include "dihmeetlem9N.mm"
include "syl121anc.mm"
include "3eqtr3rd.mm"

theorem dihmeetlem12N
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume dihmeetlem9.b: |- B = ( Base ` K )
  assume dihmeetlem9.l: |- .<_ = ( le ` K )
  assume dihmeetlem9.h: |- H = ( LHyp ` K )
  assume dihmeetlem9.j: |- .\/ = ( join ` K )
  assume dihmeetlem9.m: |- ./\ = ( meet ` K )
  assume dihmeetlem9.a: |- A = ( Atoms ` K )
  assume dihmeetlem9.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihmeetlem9.s: |- .(+) = ( LSSum ` U )
  assume dihmeetlem9.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ Y e. B ) /\ ( ( p e. A /\ -. p .<_ W ) /\ p .<_ X /\ ( X ./\ Y ) .<_ W ) ) -> ( ( I ` ( X ./\ Y ) ) .(+) ( ( I ` p ) i^i ( I ` Y ) ) ) = ( ( I ` X ) i^i ( I ` Y ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    vp
    cv
    #
    cA
    wcel
    #
    @4
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @4
    cX
    c.le
    wbr
    #
    cX
    cY
    c.an
    co
    #
    cW
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    @9
    @4
    c.or
    co
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    cin
    #
    @4
    cI
    cfv
    #
    @9
    cI
    cfv
    #
    c.po
    co
    #
    @14
    cin
    #
    cX
    cI
    cfv
    @14
    cin
    #
    @17
    @16
    @14
    cin
    c.po
    co
    #
    @12
    @13
    @18
    @14
    @12
    @0
    @1
    @2
    @7
    @8
    @10
    @13
    @18
    wceq
    @0
    @1
    @2
    @11
    simpl1
    #
    @0
    @1
    @2
    @11
    simpl2
    #
    @0
    @1
    @2
    @11
    simpl3
    #
    @3
    @7
    @8
    @10
    simpr1
    @3
    @7
    @8
    @10
    simpr2
    @3
    @7
    @8
    @10
    simpr3
    cA
    cB
    c.po
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cY
    vp
    dihmeetlem9.b
    dihmeetlem9.l
    dihmeetlem9.h
    dihmeetlem9.j
    dihmeetlem9.m
    dihmeetlem9.a
    dihmeetlem9.u
    dihmeetlem9.s
    dihmeetlem9.i
    dihmeetlem8N
    syl312anc
    ineq1d
    @3
    @7
    @8
    @15
    @20
    wceq
    @10
    cA
    cB
    c.po
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cY
    vp
    dihmeetlem9.b
    dihmeetlem9.l
    dihmeetlem9.h
    dihmeetlem9.j
    dihmeetlem9.m
    dihmeetlem9.a
    dihmeetlem9.u
    dihmeetlem9.s
    dihmeetlem9.i
    dihmeetlem11N
    3adantr3
    @12
    @0
    @1
    @2
    @5
    @19
    @21
    wceq
    @22
    @23
    @24
    @5
    @6
    @8
    @10
    @3
    simpr1l
    cA
    cB
    c.po
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cY
    vp
    dihmeetlem9.b
    dihmeetlem9.l
    dihmeetlem9.h
    dihmeetlem9.j
    dihmeetlem9.m
    dihmeetlem9.a
    dihmeetlem9.u
    dihmeetlem9.s
    dihmeetlem9.i
    dihmeetlem9N
    syl121anc
    3eqtr3rd
end
