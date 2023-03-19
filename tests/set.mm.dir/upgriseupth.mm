include "cupgr.mm"
include "wcel.mm"
include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cdm.mm"
include "wf1o.mm"
include "wa.mm"
include "cword.mm"
include "cfz.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "wb.mm"
include "iseupthf1o.mm"
include "a1i.mm"
include "upgriswlk.mm"
include "anbi1d.mm"
include "simpr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "3jca.mm"
include "f1of.mm"
include "iswrdi.mm"
include "syl.mm"
include "3anim1i.mm"
include "simp1.mm"
include "jca.mm"
include "impbii.mm"
include "3bitrd.mm"

theorem upgriseupth
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  let cN: class N
  assume eupths.i: |- I = ( iEdg ` G )
  assume upgriseupth.v: |- V = ( Vtx ` G )

  disjoint F k
  disjoint G k
  disjoint I k
  disjoint P k
  disjoint V k
  disjoint G f
  disjoint G g
  disjoint G p
  disjoint f g
  disjoint f p
  disjoint g p
  disjoint I g
  disjoint F f
  disjoint F p
  disjoint I f
  disjoint I p
  disjoint P f
  disjoint P p
  disjoint N k
  assert |- ( G e. UPGraph -> ( F ( EulerPaths ` G ) P <-> ( F : ( 0 ..^ ( # ` F ) ) -1-1-onto-> dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } ) ) )

  proof
    cG
    cupgr
    wcel
    #
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cI
    cdm
    #
    cF
    wf1o
    #
    wa
    #
    cF
    @5
    cword
    wcel
    #
    cc0
    @3
    cfz
    co
    cV
    cP
    wf
    #
    vk
    cv
    #
    cF
    cfv
    cI
    cfv
    @10
    cP
    cfv
    @10
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    vk
    @4
    wral
    #
    w3a
    #
    @6
    wa
    #
    @6
    @9
    @11
    w3a
    #
    @1
    @7
    wb
    @0
    cP
    cF
    cG
    cI
    eupths.i
    iseupthf1o
    a1i
    @0
    @2
    @12
    @6
    cP
    vk
    cF
    cG
    cI
    cV
    upgriseupth.v
    eupths.i
    upgriswlk
    anbi1d
    @13
    @14
    wb
    @0
    @13
    @14
    @13
    @6
    @9
    @11
    @12
    @6
    simpr
    @8
    @9
    @11
    @6
    simpl2
    @8
    @9
    @11
    @6
    simpl3
    3jca
    @14
    @12
    @6
    @6
    @8
    @9
    @11
    @6
    @4
    @5
    cF
    wf
    @8
    @4
    @5
    cF
    f1of
    @5
    @3
    cF
    iswrdi
    syl
    3anim1i
    @6
    @9
    @11
    simp1
    jca
    impbii
    a1i
    3bitrd
end
