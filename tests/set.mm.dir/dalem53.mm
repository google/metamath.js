include "wceq.mm"
include "w3a.mm"
include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "dalem51.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "atbase.mm"
include "anim2i.mm"
include "3anim1i.mm"
include "biid.mm"
include "dalem15.mm"
include "syl3anl1.mm"
include "syl.mm"

theorem dalem53
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cY: class Y
  let cZ: class Z
  let vc: setvar c
  let vd: setvar d
  assume dalem.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalem.l: |- .<_ = ( le ` K )
  assume dalem.j: |- .\/ = ( join ` K )
  assume dalem.a: |- A = ( Atoms ` K )
  assume dalem.ps: |- ( ps <-> ( ( c e. A /\ d e. A ) /\ -. c .<_ Y /\ ( d =/= c /\ -. d .<_ Y /\ C .<_ ( c .\/ d ) ) ) )
  assume dalem53.m: |- ./\ = ( meet ` K )
  assume dalem53.n: |- N = ( LLines ` K )
  assume dalem53.o: |- O = ( LPlanes ` K )
  assume dalem53.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem53.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem53.g: |- G = ( ( c .\/ P ) ./\ ( d .\/ S ) )
  assume dalem53.h: |- H = ( ( c .\/ Q ) ./\ ( d .\/ T ) )
  assume dalem53.i: |- I = ( ( c .\/ R ) ./\ ( d .\/ U ) )
  assume dalem53.b1: |- B = ( ( ( G .\/ H ) .\/ I ) ./\ Y )


  assert |- ( ( ph /\ Y = Z /\ ps ) -> B e. N )

  proof
    wph
    cY
    cZ
    wceq
    wps
    w3a
    cK
    chlt
    wcel
    #
    vc
    cv
    #
    cA
    wcel
    #
    wa
    #
    cG
    cA
    wcel
    cH
    cA
    wcel
    cI
    cA
    wcel
    w3a
    #
    cP
    cA
    wcel
    cQ
    cA
    wcel
    cR
    cA
    wcel
    w3a
    #
    w3a
    #
    cG
    cH
    c.or
    co
    #
    cI
    c.or
    co
    #
    cO
    wcel
    cY
    cO
    wcel
    wa
    #
    @1
    @7
    c.le
    wbr
    wn
    @1
    cH
    cI
    c.or
    co
    c.le
    wbr
    wn
    @1
    cI
    cG
    c.or
    co
    c.le
    wbr
    wn
    w3a
    @1
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    @1
    cQ
    cR
    c.or
    co
    c.le
    wbr
    wn
    @1
    cR
    cP
    c.or
    co
    c.le
    wbr
    wn
    w3a
    @1
    cG
    cP
    c.or
    co
    c.le
    wbr
    @1
    cH
    cQ
    c.or
    co
    c.le
    wbr
    @1
    cI
    cR
    c.or
    co
    c.le
    wbr
    w3a
    w3a
    #
    w3a
    @8
    cY
    wne
    #
    wa
    cB
    cN
    wcel
    #
    wph
    wps
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    cG
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cO
    cY
    cZ
    vc
    vd
    dalem.ph
    dalem.l
    dalem.j
    dalem.a
    dalem.ps
    dalem53.m
    dalem53.o
    dalem53.y
    dalem53.z
    dalem53.g
    dalem53.h
    dalem53.i
    dalem51
    @6
    @0
    @1
    cK
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @4
    @5
    w3a
    #
    @9
    @10
    @11
    @12
    @3
    @15
    @4
    @5
    @2
    @14
    @0
    cA
    @13
    @1
    cK
    @13
    eqid
    dalem.a
    atbase
    anim2i
    3anim1i
    @16
    @9
    @10
    w3a
    #
    cA
    @1
    cG
    cH
    cI
    cP
    cQ
    cR
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cB
    @8
    cY
    @17
    biid
    dalem.l
    dalem.j
    dalem.a
    dalem53.m
    dalem53.n
    dalem53.o
    @8
    eqid
    dalem53.y
    dalem53.b1
    dalem15
    syl3anl1
    syl
end
