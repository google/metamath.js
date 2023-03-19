include "wceq.mm"
include "w3a.mm"
include "clat.mm"
include "wcel.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "dalemkelat.mm"
include "3ad2ant1.mm"
include "dalemcceb.mm"
include "3ad2ant3.mm"
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
include "dalem44.mm"
include "latnlej2l.mm"
include "syl131anc.mm"

theorem dalem45
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
  assume dalem44.m: |- ./\ = ( meet ` K )
  assume dalem44.o: |- O = ( LPlanes ` K )
  assume dalem44.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem44.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem44.g: |- G = ( ( c .\/ P ) ./\ ( d .\/ S ) )
  assume dalem44.h: |- H = ( ( c .\/ Q ) ./\ ( d .\/ T ) )
  assume dalem44.i: |- I = ( ( c .\/ R ) ./\ ( d .\/ U ) )


  assert |- ( ( ph /\ Y = Z /\ ps ) -> -. c .<_ ( G .\/ H ) )

  proof
    wph
    cY
    cZ
    wceq
    #
    wps
    w3a
    #
    cK
    clat
    wcel
    #
    vc
    cv
    #
    cK
    cbs
    cfv
    #
    wcel
    #
    cG
    cH
    c.or
    co
    #
    @4
    wcel
    #
    cI
    @4
    wcel
    #
    @3
    @6
    cI
    c.or
    co
    c.le
    wbr
    wn
    @3
    @6
    c.le
    wbr
    wn
    wph
    @0
    @2
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
    wps
    wph
    @5
    @0
    wps
    cA
    cC
    c.or
    cK
    c.le
    cY
    vc
    vd
    dalem.ps
    dalem.a
    dalemcceb
    3ad2ant3
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
    dalem44.m
    dalem44.o
    dalem44.y
    dalem44.z
    dalem44.g
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
    dalem44.m
    dalem44.o
    dalem44.y
    dalem44.z
    dalem44.h
    dalem29
    cA
    @4
    c.or
    cK
    cG
    cH
    @4
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
    dalem44.m
    dalem44.o
    dalem44.y
    dalem44.z
    dalem44.i
    dalem34
    cA
    @4
    cI
    cK
    @10
    dalem.a
    atbase
    syl
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
    dalem44.m
    dalem44.o
    dalem44.y
    dalem44.z
    dalem44.g
    dalem44.h
    dalem44.i
    dalem44
    @4
    c.or
    cK
    c.le
    @3
    @6
    cI
    @10
    dalem.l
    dalem.j
    latnlej2l
    syl131anc
end
