include "wne.mm"
include "wa.mm"
include "chlt.mm"
include "wcel.mm"
include "clvol.mm"
include "cfv.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "dalemkehl.mm"
include "adantr.mm"
include "dalemyeo.mm"
include "dalemzeo.mm"
include "eqid.mm"
include "dalem9.mm"
include "clat.mm"
include "cbs.mm"
include "dalemkelat.mm"
include "dalemyeb.mm"
include "dalemceb.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "syl6breqr.mm"
include "dalem8.mm"
include "simpr.mm"
include "2lplnj.mm"
include "syl133anc.mm"

theorem dalem13
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cO: class O
  let cW: class W
  let cY: class Y
  let cZ: class Z
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalem13.o: |- O = ( LPlanes ` K )
  assume dalem13.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem13.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem13.w: |- W = ( Y .\/ C )


  assert |- ( ( ph /\ Y =/= Z ) -> ( Y .\/ Z ) = W )

  proof
    wph
    cY
    cZ
    wne
    #
    wa
    cK
    chlt
    wcel
    #
    cY
    cO
    wcel
    #
    cZ
    cO
    wcel
    #
    cW
    cK
    clvol
    cfv
    #
    wcel
    cY
    cW
    c.le
    wbr
    #
    cZ
    cW
    c.le
    wbr
    #
    @0
    cY
    cZ
    c.or
    co
    cW
    wceq
    wph
    @1
    @0
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
    dalema.ph
    dalemkehl
    adantr
    wph
    @2
    @0
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
    dalema.ph
    dalemyeo
    adantr
    wph
    @3
    @0
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
    dalema.ph
    dalemzeo
    adantr
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
    @4
    cW
    cY
    cZ
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem13.o
    @4
    eqid
    #
    dalem13.y
    dalem13.z
    dalem13.w
    dalem9
    wph
    @5
    @0
    wph
    cY
    cY
    cC
    c.or
    co
    #
    cW
    c.le
    wph
    cK
    clat
    wcel
    cY
    cK
    cbs
    cfv
    #
    wcel
    cC
    @9
    wcel
    cY
    @8
    c.le
    wbr
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
    dalema.ph
    dalemkelat
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
    dalema.ph
    dalem13.o
    dalemyeb
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
    dalema.ph
    dalemc.a
    dalemceb
    @9
    c.or
    cK
    c.le
    cY
    cC
    @9
    eqid
    dalemc.l
    dalemc.j
    latlej1
    syl3anc
    dalem13.w
    syl6breqr
    adantr
    wph
    @6
    @0
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
    cW
    cY
    cZ
    dalema.ph
    dalemc.l
    dalemc.j
    dalemc.a
    dalem13.o
    dalem13.y
    dalem13.z
    dalem13.w
    dalem8
    adantr
    wph
    @0
    simpr
    cO
    c.or
    cK
    c.le
    @4
    cW
    cY
    cZ
    dalemc.l
    dalemc.j
    dalem13.o
    @7
    2lplnj
    syl133anc
end
