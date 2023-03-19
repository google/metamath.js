include "wceq.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "clat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "dalemkelat.mm"
include "3ad2ant1.mm"
include "chlt.mm"
include "dalemkehl.mm"
include "dalem23.mm"
include "dalem29.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "dalem34.mm"
include "atbase.mm"
include "syl.mm"
include "latlej2.mm"
include "dalem35.mm"
include "nbrne1.mm"
include "syl2anc.mm"

theorem dalem43
  let wph: wff ph
  let wps: wff ps
  let cA: class A
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
  assume dalem38.m: |- ./\ = ( meet ` K )
  assume dalem38.o: |- O = ( LPlanes ` K )
  assume dalem38.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem38.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem38.g: |- G = ( ( c .\/ P ) ./\ ( d .\/ S ) )
  assume dalem38.h: |- H = ( ( c .\/ Q ) ./\ ( d .\/ T ) )
  assume dalem38.i: |- I = ( ( c .\/ R ) ./\ ( d .\/ U ) )


  assert |- ( ( ph /\ Y = Z /\ ps ) -> ( ( G .\/ H ) .\/ I ) =/= Y )

  proof
    wph
    cY
    cZ
    wceq
    #
    wps
    w3a
    #
    cI
    cG
    cH
    c.or
    co
    #
    cI
    c.or
    co
    #
    c.le
    wbr
    #
    cI
    cY
    c.le
    wbr
    wn
    @3
    cY
    wne
    @1
    cK
    clat
    wcel
    #
    @2
    cK
    cbs
    cfv
    #
    wcel
    #
    cI
    @6
    wcel
    #
    @4
    wph
    @0
    @5
    wps
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalem.ph
    dalemkelat
    3ad2ant1
    @1
    cK
    chlt
    wcel
    #
    cG
    cA
    wcel
    cH
    cA
    wcel
    @7
    wph
    @0
    @9
    wps
    wph
    cA
    cC
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    cO
    cY
    cZ
    dalem.ph
    dalemkehl
    3ad2ant1
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
    dalem38.m
    dalem38.o
    dalem38.y
    dalem38.z
    dalem38.g
    dalem23
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
    cH
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
    dalem38.m
    dalem38.o
    dalem38.y
    dalem38.z
    dalem38.h
    dalem29
    cA
    @6
    c.or
    cK
    cG
    cH
    @6
    eqid
    #
    dalem.j
    dalem.a
    hlatjcl
    syl3anc
    @1
    cI
    cA
    wcel
    @8
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
    dalem38.m
    dalem38.o
    dalem38.y
    dalem38.z
    dalem38.i
    dalem34
    cA
    @6
    cI
    cK
    @10
    dalem.a
    atbase
    syl
    @6
    c.or
    cK
    c.le
    @2
    cI
    @10
    dalem.l
    dalem.j
    latlej2
    syl3anc
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
    dalem38.m
    dalem38.o
    dalem38.y
    dalem38.z
    dalem38.i
    dalem35
    cI
    @3
    cY
    c.le
    nbrne1
    syl2anc
end
