include "chlt.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "simp11.mm"
include "simp13.mm"
include "simp12.mm"
include "3jca.mm"
include "simp2.mm"
include "ancomd.mm"
include "simp32.mm"
include "simp31.mm"
include "dalemclpjs.mm"
include "wceq.mm"
include "dalemkehl.mm"
include "dalempea.mm"
include "dalemsea.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breqtrd.mm"
include "dalemclqjt.mm"
include "dalemqea.mm"
include "dalemtea.mm"
include "dalemclrju.mm"
include "dalemrea.mm"
include "dalemuea.mm"
include "sylbir.mm"
include "sylbi.mm"

theorem dalemswapyz
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


  assert |- ( ph -> ( ( ( K e. HL /\ C e. ( Base ` K ) ) /\ ( S e. A /\ T e. A /\ U e. A ) /\ ( P e. A /\ Q e. A /\ R e. A ) ) /\ ( Z e. O /\ Y e. O ) /\ ( ( -. C .<_ ( S .\/ T ) /\ -. C .<_ ( T .\/ U ) /\ -. C .<_ ( U .\/ S ) ) /\ ( -. C .<_ ( P .\/ Q ) /\ -. C .<_ ( Q .\/ R ) /\ -. C .<_ ( R .\/ P ) ) /\ ( C .<_ ( S .\/ P ) /\ C .<_ ( T .\/ Q ) /\ C .<_ ( U .\/ R ) ) ) ) )

  proof
    wph
    cK
    chlt
    wcel
    #
    cC
    cK
    cbs
    cfv
    wcel
    wa
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    w3a
    #
    cS
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    cU
    cA
    wcel
    #
    w3a
    #
    w3a
    #
    cY
    cO
    wcel
    #
    cZ
    cO
    wcel
    #
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
    cC
    cS
    cT
    c.or
    co
    c.le
    wbr
    wn
    cC
    cT
    cU
    c.or
    co
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
    w3a
    #
    cC
    cP
    cS
    c.or
    co
    #
    c.le
    wbr
    cC
    cQ
    cT
    c.or
    co
    #
    c.le
    wbr
    cC
    cR
    cU
    c.or
    co
    #
    c.le
    wbr
    w3a
    #
    w3a
    #
    w3a
    #
    @1
    @9
    @5
    w3a
    #
    @12
    @11
    wa
    #
    @15
    @14
    cC
    cS
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    cC
    cT
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cC
    cU
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    w3a
    dalema.ph
    @21
    @22
    @23
    @31
    @21
    @1
    @9
    @5
    @1
    @5
    @9
    @13
    @20
    simp11
    @1
    @5
    @9
    @13
    @20
    simp13
    @1
    @5
    @9
    @13
    @20
    simp12
    3jca
    @21
    @11
    @12
    @10
    @13
    @20
    simp2
    ancomd
    @21
    @15
    @14
    @30
    @10
    @13
    @14
    @15
    @19
    simp32
    @10
    @13
    @14
    @15
    @19
    simp31
    @21
    wph
    @30
    dalema.ph
    wph
    @25
    @27
    @29
    wph
    cC
    @16
    @24
    c.le
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
    wph
    @0
    @2
    @6
    @16
    @24
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
    dalempea
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
    cP
    cS
    dalemc.j
    dalemc.a
    hlatjcom
    syl3anc
    breqtrd
    wph
    cC
    @17
    @26
    c.le
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
    dalemclqjt
    wph
    @0
    @3
    @7
    @17
    @26
    wceq
    @32
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
    dalemqea
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
    dalemtea
    cA
    c.or
    cK
    cQ
    cT
    dalemc.j
    dalemc.a
    hlatjcom
    syl3anc
    breqtrd
    wph
    cC
    @18
    @28
    c.le
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
    dalemclrju
    wph
    @0
    @4
    @8
    @18
    @28
    wceq
    @32
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
    dalemrea
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
    dalemuea
    cA
    c.or
    cK
    cR
    cU
    dalemc.j
    dalemc.a
    hlatjcom
    syl3anc
    breqtrd
    3jca
    sylbir
    3jca
    3jca
    sylbi
end
