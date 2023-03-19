include "co.mm"
include "wbr.mm"
include "dalem6.mm"
include "dalem7.mm"
include "clat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "wb.mm"
include "dalemkelat.mm"
include "dalemseb.mm"
include "dalemteb.mm"
include "dalemyeb.mm"
include "dalemceb.mm"
include "eqid.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "dalem5.mm"
include "dalemsjteb.mm"
include "dalemueb.mm"
include "syl5eqbr.mm"

theorem dalem8
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
  assume dalem6.o: |- O = ( LPlanes ` K )
  assume dalem6.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem6.z: |- Z = ( ( S .\/ T ) .\/ U )
  assume dalem6.w: |- W = ( Y .\/ C )


  assert |- ( ph -> Z .<_ W )

  proof
    wph
    cZ
    cS
    cT
    c.or
    co
    #
    cU
    c.or
    co
    #
    cW
    c.le
    dalem6.z
    wph
    @0
    cW
    c.le
    wbr
    #
    cU
    cW
    c.le
    wbr
    #
    @1
    cW
    c.le
    wbr
    #
    wph
    cS
    cW
    c.le
    wbr
    #
    cT
    cW
    c.le
    wbr
    #
    @2
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
    dalem6.o
    dalem6.y
    dalem6.z
    dalem6.w
    dalem6
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
    dalem6.o
    dalem6.y
    dalem6.z
    dalem6.w
    dalem7
    wph
    cK
    clat
    wcel
    #
    cS
    cK
    cbs
    cfv
    #
    wcel
    cT
    @8
    wcel
    cW
    @8
    wcel
    #
    @5
    @6
    wa
    @2
    wb
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
    #
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
    cW
    cY
    cC
    c.or
    co
    #
    @8
    dalem6.w
    wph
    @7
    cY
    @8
    wcel
    cC
    @8
    wcel
    @11
    @8
    wcel
    @10
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
    dalem6.o
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
    @8
    c.or
    cK
    cY
    cC
    @8
    eqid
    #
    dalemc.j
    latjcl
    syl3anc
    syl5eqel
    #
    @8
    c.or
    cK
    c.le
    cS
    cT
    cW
    @12
    dalemc.l
    dalemc.j
    latjle12
    syl13anc
    mpbi2and
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
    dalem6.o
    dalem6.y
    dalem6.w
    dalem5
    wph
    @7
    @0
    @8
    wcel
    cU
    @8
    wcel
    @9
    @2
    @3
    wa
    @4
    wb
    @10
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
    dalemc.j
    dalemc.a
    dalemsjteb
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
    dalemueb
    @13
    @8
    c.or
    cK
    c.le
    @0
    cU
    cW
    @12
    dalemc.l
    dalemc.j
    latjle12
    syl13anc
    mpbi2and
    syl5eqbr
end
