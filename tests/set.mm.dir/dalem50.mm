include "wa.mm"
include "chlt.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wne.mm"
include "dalemrot.mm"
include "adantr.mm"
include "dalemrotps.mm"
include "biid.mm"
include "eqid.mm"
include "dalem49.mm"
include "syl2anc.mm"

theorem dalem50
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


  assert |- ( ( ph /\ ps ) -> -. c .<_ ( R .\/ P ) )

  proof
    wph
    wps
    wa
    cK
    chlt
    wcel
    cC
    cK
    cbs
    cfv
    wcel
    wa
    cQ
    cA
    wcel
    cR
    cA
    wcel
    cP
    cA
    wcel
    w3a
    cT
    cA
    wcel
    cU
    cA
    wcel
    cS
    cA
    wcel
    w3a
    w3a
    cQ
    cR
    c.or
    co
    #
    cP
    c.or
    co
    #
    cO
    wcel
    cT
    cU
    c.or
    co
    #
    cS
    c.or
    co
    #
    cO
    wcel
    wa
    cC
    @0
    c.le
    wbr
    wn
    cC
    cR
    cP
    c.or
    co
    #
    c.le
    wbr
    wn
    cC
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    w3a
    cC
    @2
    c.le
    wbr
    wn
    cC
    cU
    cS
    c.or
    co
    c.le
    wbr
    wn
    cC
    cS
    cT
    c.or
    co
    c.le
    wbr
    wn
    w3a
    cC
    cQ
    cT
    c.or
    co
    c.le
    wbr
    cC
    cR
    cU
    c.or
    co
    c.le
    wbr
    cC
    cP
    cS
    c.or
    co
    c.le
    wbr
    w3a
    w3a
    w3a
    #
    vc
    cv
    #
    cA
    wcel
    vd
    cv
    #
    cA
    wcel
    wa
    @6
    @1
    c.le
    wbr
    wn
    @7
    @6
    wne
    @7
    @1
    c.le
    wbr
    wn
    cC
    @6
    @7
    c.or
    co
    c.le
    wbr
    w3a
    w3a
    #
    @6
    @4
    c.le
    wbr
    wn
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
    dalem.l
    dalem.j
    dalem.a
    dalem44.y
    dalem44.z
    dalemrot
    adantr
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
    c.or
    cK
    c.le
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
    dalem44.y
    dalemrotps
    @5
    @8
    cA
    cC
    cQ
    cR
    cP
    cT
    cU
    cS
    cH
    cI
    cG
    c.or
    cK
    c.le
    c.an
    cO
    @1
    @3
    vc
    vd
    @5
    biid
    dalem.l
    dalem.j
    dalem.a
    @8
    biid
    dalem44.m
    dalem44.o
    @1
    eqid
    @3
    eqid
    dalem44.h
    dalem44.i
    dalem44.g
    dalem49
    syl2anc
end
