include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "clat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "dalemkelat.mm"
include "dalemceb.mm"
include "dalemseb.mm"
include "dalemteb.mm"
include "chlt.mm"
include "wa.mm"
include "w3a.mm"
include "simp321.mm"
include "sylbi.mm"
include "eqid.mm"
include "latnlej2l.mm"
include "syl131anc.mm"
include "wceq.mm"
include "dalemclpjs.mm"
include "oveq1.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "dalemkehl.mm"
include "dalemsea.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "sylibd.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem dalempnes
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
  let cY: class Y
  let cZ: class Z
  assume dalema.ph: |- ( ph <-> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( Y e. O /\ Z e. O ) /\ ( ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( C .<_ ( P .\/ S ) /\ C .<_ ( Q .\/ T ) /\ C .<_ ( R .\/ U ) ) ) ) )
  assume dalemc.l: |- .<_ = ( le ` K )
  assume dalemc.j: |- .\/ = ( join ` K )
  assume dalemc.a: |- A = ( Atoms ` K )
  assume dalempnes.o: |- O = ( LPlanes ` K )
  assume dalempnes.y: |- Y = ( ( P .\/ Q ) .\/ R )


  assert |- ( ph -> P =/= S )

  proof
    wph
    cC
    cS
    c.le
    wbr
    #
    wn
    #
    cP
    cS
    wne
    wph
    cK
    clat
    wcel
    cC
    cK
    cbs
    cfv
    #
    wcel
    #
    cS
    @2
    wcel
    cT
    @2
    wcel
    cC
    cS
    cT
    c.or
    co
    c.le
    wbr
    wn
    #
    @1
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
    dalemc.a
    dalemceb
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
    dalemseb
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
    dalemteb
    wph
    cK
    chlt
    wcel
    #
    @3
    wa
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
    cS
    cA
    wcel
    #
    cT
    cA
    wcel
    cU
    cA
    wcel
    w3a
    w3a
    #
    cY
    cO
    wcel
    cZ
    cO
    wcel
    wa
    #
    cC
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    cC
    cQ
    cR
    c.or
    co
    c.le
    wbr
    wn
    cC
    cR
    cP
    c.or
    co
    c.le
    wbr
    wn
    w3a
    #
    @4
    cC
    cT
    cU
    c.or
    co
    c.le
    wbr
    wn
    #
    cC
    cU
    cS
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    cC
    cP
    cS
    c.or
    co
    #
    c.le
    wbr
    #
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
    w3a
    #
    w3a
    w3a
    @4
    dalema.ph
    @4
    @10
    @11
    @9
    @14
    @7
    @8
    simp321
    sylbi
    @2
    c.or
    cK
    c.le
    cC
    cS
    cT
    @2
    eqid
    dalemc.l
    dalemc.j
    latnlej2l
    syl131anc
    wph
    @0
    cP
    cS
    wph
    cP
    cS
    wceq
    #
    cC
    cS
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    @0
    wph
    @13
    @15
    @17
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
    dalemclpjs
    @15
    @12
    @16
    cC
    c.le
    cP
    cS
    cS
    c.or
    oveq1
    breq2d
    syl5ibcom
    wph
    @16
    cS
    cC
    c.le
    wph
    @5
    @6
    @16
    cS
    wceq
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
    dalemsea
    cA
    c.or
    cK
    cS
    dalemc.j
    dalemc.a
    hlatjidm
    syl2anc
    breq2d
    sylibd
    necon3bd
    mpd
end
