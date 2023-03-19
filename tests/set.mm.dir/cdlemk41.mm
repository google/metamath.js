include "cfv.mm"
include "co.mm"
include "cv.mm"
include "ccnv.mm"
include "ccom.mm"
include "wcel.mm"
include "nfcvd.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "coeq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "syl5eq.mm"
include "csbiegf.mm"

theorem cdlemk41
  let cP: class P
  let cR: class R
  let cT: class T
  let vg: setvar g
  let cG: class G
  let c.or: class .\/
  let c.an: class ./\
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  assume cdlemk41.y: |- Y = ( ( P .\/ ( R ` g ) ) ./\ ( Z .\/ ( R ` ( g o. `' b ) ) ) )

  disjoint ./\ g
  disjoint .\/ g
  disjoint G g
  disjoint P g
  disjoint R g
  disjoint T g
  disjoint Z g
  disjoint b g
  assert |- ( G e. T -> [_ G / g ]_ Y = ( ( P .\/ ( R ` G ) ) ./\ ( Z .\/ ( R ` ( G o. `' b ) ) ) ) )

  proof
    vg
    cG
    cY
    cP
    cG
    cR
    cfv
    #
    c.or
    co
    #
    cZ
    cG
    vb
    cv
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    cT
    cG
    cT
    wcel
    vg
    @6
    nfcvd
    vg
    cv
    #
    cG
    wceq
    #
    cY
    cP
    @7
    cR
    cfv
    #
    c.or
    co
    #
    cZ
    @7
    @2
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    @6
    cdlemk41.y
    @8
    @10
    @1
    @13
    @5
    c.an
    @8
    @9
    @0
    cP
    c.or
    @7
    cG
    cR
    fveq2
    oveq2d
    @8
    @12
    @4
    cZ
    c.or
    @8
    @11
    @3
    cR
    @7
    cG
    @2
    coeq1
    fveq2d
    oveq2d
    oveq12d
    syl5eq
    csbiegf
end
