include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
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
include "wlkdlem3.mm"
include "wlkdlem1.mm"
include "wlkdlem4.mm"
include "cvv.mm"
include "w3a.mm"
include "wb.mm"
include "iswlk.mm"
include "syl3anc.mm"
include "mpbir3and.mm"

theorem wlkd
  let wph: wff ph
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  assume wlkd.p: |- ( ph -> P e. Word _V )
  assume wlkd.f: |- ( ph -> F e. Word _V )
  assume wlkd.l: |- ( ph -> ( # ` P ) = ( ( # ` F ) + 1 ) )
  assume wlkd.e: |- ( ph -> A. k e. ( 0 ..^ ( # ` F ) ) { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) )
  assume wlkd.n: |- ( ph -> A. k e. ( 0 ..^ ( # ` F ) ) ( P ` k ) =/= ( P ` ( k + 1 ) ) )
  assume wlkd.g: |- ( ph -> G e. W )
  assume wlkd.v: |- V = ( Vtx ` G )
  assume wlkd.i: |- I = ( iEdg ` G )
  assume wlkd.a: |- ( ph -> A. k e. ( 0 ... ( # ` F ) ) ( P ` k ) e. V )

  disjoint F k
  disjoint P k
  disjoint I k
  disjoint k ph
  disjoint G k
  disjoint V k
  assert |- ( ph -> F ( Walks ` G ) P )

  proof
    wph
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    cI
    cdm
    cword
    wcel
    #
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
    #
    vk
    cv
    #
    cP
    cfv
    #
    @4
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @4
    cF
    cfv
    cI
    cfv
    #
    @5
    csn
    wceq
    @5
    @6
    cpr
    @7
    wss
    wif
    vk
    cc0
    @2
    cfzo
    co
    wral
    #
    wph
    cP
    vk
    cF
    cI
    wlkd.p
    wlkd.f
    wlkd.l
    wlkd.e
    wlkdlem3
    wph
    cP
    vk
    cF
    cV
    wlkd.p
    wlkd.f
    wlkd.l
    wlkd.a
    wlkdlem1
    wph
    cP
    vk
    cF
    cI
    wlkd.p
    wlkd.f
    wlkd.l
    wlkd.e
    wlkd.n
    wlkdlem4
    wph
    cG
    cW
    wcel
    cF
    cvv
    cword
    #
    wcel
    cP
    @9
    wcel
    @0
    @1
    @3
    @8
    w3a
    wb
    wlkd.g
    wlkd.f
    wlkd.p
    cP
    @9
    vk
    cF
    cG
    cI
    cV
    cW
    @9
    wlkd.v
    wlkd.i
    iswlk
    syl3anc
    mpbir3and
end
