include "clat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
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
include "latnlej1l.mm"
include "syl131anc.mm"

theorem dalemcnes
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


  assert |- ( ph -> C =/= S )

  proof
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
    @0
    wcel
    cT
    @0
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
    cC
    cS
    wne
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
    @1
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
    @2
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
    c.le
    wbr
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
    @2
    dalema.ph
    @2
    @6
    @7
    @5
    @8
    @3
    @4
    simp321
    sylbi
    @0
    c.or
    cK
    c.le
    cC
    cS
    cT
    @0
    eqid
    dalemc.l
    dalemc.j
    latnlej1l
    syl131anc
end
