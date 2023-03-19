include "cclwlks.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "cvv.mm"
include "cxp.mm"
include "wb.mm"
include "elfvex.mm"
include "cwlks.mm"
include "wbr.mm"
include "copab.mm"
include "clwlks.mm"
include "a1i.mm"
include "eleq2d.mm"
include "elopaelxp.mm"
include "anim2i.mm"
include "ex.mm"
include "sylbid.mm"
include "mpcom.mm"
include "clwlkcomp.mm"
include "syl.mm"
include "ibi.mm"

theorem clwlkcompim
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  assume isclwlke.v: |- V = ( Vtx ` G )
  assume isclwlke.i: |- I = ( iEdg ` G )
  assume clwlkcomp.1: |- F = ( 1st ` W )
  assume clwlkcomp.2: |- P = ( 2nd ` W )

  disjoint F k
  disjoint G k
  disjoint P k
  disjoint I k
  disjoint V k
  disjoint G f
  disjoint G g
  disjoint f g
  disjoint W f
  disjoint W g
  assert |- ( W e. ( ClWalks ` G ) -> ( ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V ) /\ ( A. k e. ( 0 ..^ ( # ` F ) ) if- ( ( P ` k ) = ( P ` ( k + 1 ) ) , ( I ` ( F ` k ) ) = { ( P ` k ) } , { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) ) /\ ( P ` 0 ) = ( P ` ( # ` F ) ) ) ) )

  proof
    cW
    cG
    cclwlks
    cfv
    #
    wcel
    #
    cF
    cI
    cdm
    cword
    wcel
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    cV
    cP
    wf
    wa
    vk
    cv
    #
    cP
    cfv
    #
    @3
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @3
    cF
    cfv
    cI
    cfv
    #
    @4
    csn
    wceq
    @4
    @5
    cpr
    @6
    wss
    wif
    vk
    cc0
    @2
    cfzo
    co
    wral
    cc0
    cP
    cfv
    @2
    cP
    cfv
    wceq
    wa
    wa
    #
    @1
    cG
    cvv
    wcel
    #
    cW
    cvv
    cvv
    cxp
    wcel
    #
    wa
    #
    @1
    @7
    wb
    @8
    @1
    @10
    cW
    cG
    cclwlks
    elfvex
    @8
    @1
    cW
    vf
    cv
    #
    vg
    cv
    #
    cG
    cwlks
    cfv
    wbr
    cc0
    @12
    cfv
    @11
    chash
    cfv
    @12
    cfv
    wceq
    wa
    #
    vf
    vg
    copab
    #
    wcel
    #
    @10
    @8
    @0
    @14
    cW
    @0
    @14
    wceq
    @8
    vf
    cG
    vg
    clwlks
    a1i
    eleq2d
    @8
    @15
    @10
    @15
    @9
    @8
    @13
    vf
    vg
    cW
    elopaelxp
    anim2i
    ex
    sylbid
    mpcom
    cP
    cvv
    cvv
    vk
    cF
    cG
    cI
    cV
    cW
    cvv
    isclwlke.v
    isclwlke.i
    clwlkcomp.1
    clwlkcomp.2
    clwlkcomp
    syl
    ibi
end
