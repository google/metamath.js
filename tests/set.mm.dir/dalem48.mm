include "wa.mm"
include "clat.mm"
include "wcel.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "dalemkelat.mm"
include "adantr.mm"
include "dalemcceb.mm"
include "adantl.mm"
include "dalempjqeb.mm"
include "dalemreb.mm"
include "dalem-ccly.mm"
include "breq2i.mm"
include "sylnib.mm"
include "eqid.mm"
include "latnlej2l.mm"
include "syl131anc.mm"

theorem dalem48
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


  assert |- ( ( ph /\ ps ) -> -. c .<_ ( P .\/ Q ) )

  proof
    wph
    wps
    wa
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
    cP
    cQ
    c.or
    co
    #
    @2
    wcel
    #
    cR
    @2
    wcel
    #
    @1
    @4
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @1
    @4
    c.le
    wbr
    wn
    wph
    @0
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
    adantr
    wps
    @3
    wph
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
    adantl
    wph
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
    dalem.j
    dalem.a
    dalempjqeb
    adantr
    wph
    @6
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
    dalem.a
    dalemreb
    adantr
    wps
    @9
    wph
    wps
    @1
    cY
    c.le
    wbr
    @8
    wps
    cA
    cC
    c.or
    c.le
    cY
    vc
    vd
    dalem.ps
    dalem-ccly
    cY
    @7
    @1
    c.le
    dalem44.y
    breq2i
    sylnib
    adantl
    @2
    c.or
    cK
    c.le
    @1
    @4
    cR
    @2
    eqid
    dalem.l
    dalem.j
    latnlej2l
    syl131anc
end
