include "ceupth.mm"
include "cfv.mm"
include "cv.mm"
include "ctrls.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cdm.mm"
include "wfo.mm"
include "wa.mm"
include "copab.mm"
include "wceq.mm"
include "wtru.mm"
include "ciedg.mm"
include "wb.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "dmeqd.mm"
include "foeq3.mm"
include "syl.mm"
include "adantl.mm"
include "cvv.mm"
include "wcel.mm"
include "cwlks.mm"
include "wksv.mm"
include "trliswlk.mm"
include "ssopab2i.mm"
include "ssexi.mm"
include "a1i.mm"
include "df-eupth.mm"
include "fvmptopab.mm"
include "trud.mm"

theorem eupths
  let vf: setvar f
  let cG: class G
  let cI: class I
  let vp: setvar p
  let vg: setvar g
  assume eupths.i: |- I = ( iEdg ` G )

  disjoint G f
  disjoint G p
  disjoint f p
  disjoint G g
  disjoint f g
  disjoint g p
  disjoint I g
  assert |- ( EulerPaths ` G ) = { <. f , p >. | ( f ( Trails ` G ) p /\ f : ( 0 ..^ ( # ` f ) ) -onto-> dom I ) }

  proof
    cG
    ceupth
    cfv
    vf
    cv
    #
    vp
    cv
    #
    cG
    ctrls
    cfv
    wbr
    #
    cc0
    @0
    chash
    cfv
    cfzo
    co
    #
    cI
    cdm
    #
    @0
    wfo
    #
    wa
    vf
    vp
    copab
    wceq
    wtru
    @5
    @3
    vg
    cv
    #
    ciedg
    cfv
    #
    cdm
    #
    @0
    wfo
    #
    vf
    vp
    vg
    ctrls
    ceupth
    cG
    @6
    cG
    wceq
    #
    @9
    @5
    wb
    #
    wtru
    @10
    @8
    @4
    wceq
    @11
    @10
    @7
    cI
    @10
    @7
    cG
    ciedg
    cfv
    cI
    @6
    cG
    ciedg
    fveq2
    eupths.i
    syl6eqr
    dmeqd
    @8
    @4
    @3
    @0
    foeq3
    syl
    adantl
    @2
    vf
    vp
    copab
    #
    cvv
    wcel
    wtru
    @12
    @0
    @1
    cG
    cwlks
    cfv
    wbr
    #
    vf
    vp
    copab
    vf
    cG
    vp
    wksv
    @2
    @13
    vf
    vp
    @1
    @0
    cG
    trliswlk
    ssopab2i
    ssexi
    a1i
    vf
    vg
    vp
    df-eupth
    fvmptopab
    trud
end
