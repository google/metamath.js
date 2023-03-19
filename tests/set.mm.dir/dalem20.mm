include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "co.mm"
include "w3a.mm"
include "wrex.mm"
include "wex.mm"
include "dalem18.mm"
include "adantr.mm"
include "wcel.mm"
include "dalem19.mm"
include "ex.mm"
include "ancld.mm"
include "reximdva.mm"
include "mpd.mm"
include "3anass.mm"
include "bitri.mm"
include "2exbii.mm"
include "r2ex.mm"
include "r19.42v.mm"
include "rexbii.mm"
include "3bitr2ri.mm"
include "sylib.mm"

theorem dalem20
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
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
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
  assume dalem20.o: |- O = ( LPlanes ` K )
  assume dalem20.y: |- Y = ( ( P .\/ Q ) .\/ R )
  assume dalem20.z: |- Z = ( ( S .\/ T ) .\/ U )

  disjoint c d
  disjoint A c
  disjoint A d
  disjoint C d
  disjoint K d
  disjoint .<_ c
  disjoint .<_ d
  disjoint Y c
  disjoint Y d
  disjoint .\/ c
  disjoint P c
  disjoint Q c
  disjoint R c
  disjoint Z c
  disjoint c ph
  assert |- ( ( ph /\ Y = Z ) -> E. c E. d ps )

  proof
    wph
    cY
    cZ
    wceq
    #
    wa
    #
    vc
    cv
    #
    cY
    c.le
    wbr
    wn
    #
    vd
    cv
    #
    @2
    wne
    @4
    cY
    c.le
    wbr
    wn
    cC
    @2
    @4
    c.or
    co
    c.le
    wbr
    w3a
    #
    vd
    cA
    wrex
    #
    wa
    #
    vc
    cA
    wrex
    #
    wps
    vd
    wex
    vc
    wex
    #
    @1
    @3
    vc
    cA
    wrex
    #
    @8
    wph
    @10
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
    vc
    dalem.ph
    dalem.l
    dalem.j
    dalem.a
    dalem20.y
    dalem18
    adantr
    @1
    @3
    @7
    vc
    cA
    @1
    @2
    cA
    wcel
    #
    wa
    #
    @3
    @6
    @12
    @3
    @6
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
    vc
    vd
    dalem.ph
    dalem.l
    dalem.j
    dalem.a
    dalem20.o
    dalem20.y
    dalem20.z
    dalem19
    ex
    ancld
    reximdva
    mpd
    @9
    @11
    @4
    cA
    wcel
    wa
    #
    @3
    @5
    wa
    #
    wa
    #
    vd
    wex
    vc
    wex
    @14
    vd
    cA
    wrex
    #
    vc
    cA
    wrex
    @8
    wps
    @15
    vc
    vd
    wps
    @13
    @3
    @5
    w3a
    @15
    dalem.ps
    @13
    @3
    @5
    3anass
    bitri
    2exbii
    @14
    vc
    vd
    cA
    cA
    r2ex
    @16
    @7
    vc
    cA
    @3
    @5
    vd
    cA
    r19.42v
    rexbii
    3bitr2ri
    sylib
end
