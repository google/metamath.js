include "cpths.mm"
include "cfv.mm"
include "cv.mm"
include "ctrls.mm"
include "wbr.mm"
include "c1.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "cc0.mm"
include "cpr.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "w3a.mm"
include "wtru.mm"
include "biidd.mm"
include "cvv.mm"
include "wcel.mm"
include "cwlks.mm"
include "wksv.mm"
include "trliswlk.mm"
include "ssopab2i.mm"
include "ssexi.mm"
include "a1i.mm"
include "cmpt.mm"
include "df-pths.mm"
include "3anass.mm"
include "opabbii.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "fvmptopab.mm"
include "trud.mm"
include "bicomi.mm"

theorem pthsfval
  let vf: setvar f
  let cG: class G
  let vp: setvar p
  let vg: setvar g

  disjoint G f
  disjoint G p
  disjoint f p
  disjoint G g
  disjoint f g
  disjoint g p
  assert |- ( Paths ` G ) = { <. f , p >. | ( f ( Trails ` G ) p /\ Fun `' ( p |` ( 1 ..^ ( # ` f ) ) ) /\ ( ( p " { 0 , ( # ` f ) } ) i^i ( p " ( 1 ..^ ( # ` f ) ) ) ) = (/) ) }

  proof
    cG
    cpths
    cfv
    #
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
    @2
    c1
    @1
    chash
    cfv
    #
    cfzo
    co
    #
    cres
    ccnv
    wfun
    #
    @2
    cc0
    @4
    cpr
    cima
    @2
    @5
    cima
    cin
    c0
    wceq
    #
    wa
    #
    wa
    #
    vf
    vp
    copab
    #
    @3
    @6
    @7
    w3a
    #
    vf
    vp
    copab
    @0
    @10
    wceq
    wtru
    @8
    @8
    vf
    vp
    vg
    ctrls
    cpths
    cG
    wtru
    vg
    cv
    #
    cG
    wceq
    wa
    @8
    biidd
    @3
    vf
    vp
    copab
    #
    cvv
    wcel
    wtru
    @13
    @1
    @2
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
    @3
    @14
    vf
    vp
    @2
    @1
    cG
    trliswlk
    ssopab2i
    ssexi
    a1i
    cpths
    vg
    cvv
    @1
    @2
    @12
    ctrls
    cfv
    wbr
    #
    @6
    @7
    w3a
    #
    vf
    vp
    copab
    #
    cmpt
    vg
    cvv
    @15
    @8
    wa
    #
    vf
    vp
    copab
    #
    cmpt
    vf
    vg
    vp
    df-pths
    vg
    cvv
    @17
    @19
    @16
    @18
    vf
    vp
    @15
    @6
    @7
    3anass
    opabbii
    mpteq2i
    eqtri
    fvmptopab
    trud
    @9
    @11
    vf
    vp
    @11
    @9
    @3
    @6
    @7
    3anass
    bicomi
    opabbii
    eqtri
end
