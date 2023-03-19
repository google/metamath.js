include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wi.mm"
include "weq.mm"
include "paddasslem11.mm"
include "3ad2antr3.mm"
include "ex.mm"
include "adantrd.mm"
include "a1d.mm"
include "exp31.mm"
include "wne.mm"
include "3simpb.mm"
include "3anim1i.mm"
include "3simpc.mm"
include "anim1i.mm"
include "paddasslem12.mm"
include "syl2an.mm"
include "3exp1.mm"
include "3expia.mm"
include "3simpa.mm"
include "anim12i.mm"
include "paddasslem13.mm"
include "expr.mm"
include "3expd.mm"
include "wn.mm"
include "paddasslem10.mm"
include "pm2.61d.mm"
include "impd.mm"
include "expimpd.mm"
include "3exp.mm"
include "pm2.61dne.mm"
include "3imp1.mm"

theorem paddasslem14
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vr: setvar r
  let vp: setvar p
  let vs: setvar s
  assume paddasslem.l: |- .<_ = ( le ` K )
  assume paddasslem.j: |- .\/ = ( join ` K )
  assume paddasslem.a: |- A = ( Atoms ` K )
  assume paddasslem.p: |- .+ = ( +P ` K )


  assert |- ( ( ( K e. HL /\ ( X C_ A /\ Y C_ A /\ Z C_ A ) /\ ( p e. A /\ r e. A ) ) /\ ( ( x e. X /\ y e. Y /\ z e. Z ) /\ ( p .<_ ( x .\/ r ) /\ r .<_ ( y .\/ z ) ) ) ) -> p e. ( ( X .+ Y ) .+ Z ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    cY
    cA
    wss
    cZ
    cA
    wss
    w3a
    #
    vp
    cv
    #
    cA
    wcel
    vr
    cv
    #
    cA
    wcel
    wa
    #
    vx
    cv
    #
    cX
    wcel
    #
    vy
    cv
    #
    cY
    wcel
    #
    vz
    cv
    #
    cZ
    wcel
    #
    w3a
    #
    @2
    @5
    @3
    c.or
    co
    c.le
    wbr
    #
    @3
    @7
    @9
    c.or
    co
    c.le
    wbr
    #
    wa
    #
    wa
    #
    @2
    cX
    cY
    c.pl
    co
    cZ
    c.pl
    co
    wcel
    #
    @0
    @1
    @4
    @15
    @16
    wi
    #
    wi
    #
    wi
    #
    @2
    @9
    @0
    vp
    vz
    weq
    #
    @1
    @18
    @0
    @20
    wa
    @1
    wa
    #
    @17
    @4
    @21
    @11
    @16
    @14
    @21
    @11
    @16
    @21
    @6
    @10
    @16
    @8
    vz
    cA
    c.pl
    c.or
    cK
    c.le
    cX
    cY
    cZ
    vp
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem.p
    paddasslem11
    3ad2antr3
    ex
    adantrd
    a1d
    exp31
    @0
    @2
    @9
    wne
    #
    @19
    @0
    @22
    wa
    #
    @19
    @5
    @7
    @0
    @22
    vx
    vy
    weq
    #
    @19
    @0
    @22
    @24
    w3a
    #
    @1
    @4
    @15
    @16
    @25
    @1
    @4
    w3a
    @0
    @24
    wa
    #
    @1
    @4
    w3a
    @8
    @10
    wa
    #
    @14
    wa
    @16
    @15
    @25
    @26
    @1
    @4
    @0
    @22
    @24
    3simpb
    3anim1i
    @11
    @27
    @14
    @6
    @8
    @10
    3simpc
    anim1i
    vx
    vy
    vz
    cA
    c.pl
    c.or
    cK
    c.le
    cX
    cY
    cZ
    vr
    vp
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem.p
    paddasslem12
    syl2an
    3exp1
    3expia
    @0
    @22
    @5
    @7
    wne
    #
    @19
    @0
    @22
    @28
    w3a
    #
    @1
    @4
    @17
    @29
    @1
    @4
    w3a
    #
    @11
    @14
    @16
    @30
    @11
    wa
    #
    @12
    @13
    @16
    @31
    @3
    @5
    @7
    c.or
    co
    c.le
    wbr
    #
    @12
    @13
    @16
    wi
    wi
    @31
    @32
    @12
    @13
    @16
    @30
    @11
    @32
    @12
    @13
    w3a
    #
    @16
    @30
    @23
    @1
    @4
    w3a
    @6
    @8
    wa
    #
    @32
    @12
    wa
    #
    wa
    @16
    @11
    @33
    wa
    @29
    @23
    @1
    @4
    @0
    @22
    @28
    3simpa
    3anim1i
    @11
    @34
    @33
    @35
    @6
    @8
    @10
    3simpa
    @32
    @12
    @13
    3simpa
    anim12i
    vx
    vy
    vz
    cA
    c.pl
    c.or
    cK
    c.le
    cX
    cY
    cZ
    vr
    vp
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem.p
    paddasslem13
    syl2an
    expr
    3expd
    @31
    @32
    wn
    #
    @12
    @13
    @16
    @30
    @11
    @36
    @12
    @13
    w3a
    @16
    vx
    vy
    vz
    cA
    c.pl
    c.or
    cK
    c.le
    cX
    cY
    cZ
    vr
    vp
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem.p
    paddasslem10
    expr
    3expd
    pm2.61d
    impd
    expimpd
    3exp
    3expia
    pm2.61dne
    ex
    pm2.61dne
    3imp1
end
