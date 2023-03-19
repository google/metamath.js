include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "cword.mm"
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
include "w3a.mm"
include "wi.mm"
include "wlkv.mm"
include "3simpc.mm"
include "syl.mm"
include "a1i.mm"
include "elex.mm"
include "cpm.mm"
include "ovex.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fpm.mm"
include "elexd.mm"
include "anim12i.mm"
include "3adant3.mm"
include "wb.mm"
include "iswlk.mm"
include "3expib.mm"
include "pm5.21ndd.mm"

theorem iswlkg
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vp: setvar p
  assume iswlkg.v: |- V = ( Vtx ` G )
  assume iswlkg.i: |- I = ( iEdg ` G )

  disjoint G k
  disjoint F k
  disjoint P k
  disjoint G f
  disjoint G p
  disjoint f k
  disjoint f p
  disjoint k p
  assert |- ( G e. W -> ( F ( Walks ` G ) P <-> ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) if- ( ( P ` k ) = ( P ` ( k + 1 ) ) , ( I ` ( F ` k ) ) = { ( P ` k ) } , { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) ) ) ) )

  proof
    cG
    cW
    wcel
    #
    cF
    cvv
    wcel
    #
    cP
    cvv
    wcel
    #
    wa
    #
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
    #
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
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
    @10
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @10
    cF
    cfv
    cI
    cfv
    #
    @11
    csn
    wceq
    @11
    @12
    cpr
    @13
    wss
    wif
    vk
    cc0
    @7
    cfzo
    co
    wral
    #
    w3a
    #
    @4
    @3
    wi
    @0
    @4
    cG
    cvv
    wcel
    #
    @1
    @2
    w3a
    @3
    cP
    cF
    cG
    wlkv
    @16
    @1
    @2
    3simpc
    syl
    a1i
    @15
    @3
    wi
    @0
    @6
    @9
    @3
    @14
    @6
    @1
    @9
    @2
    cF
    @5
    elex
    @9
    cP
    cV
    @8
    cpm
    co
    @8
    cV
    cP
    cc0
    @7
    cfz
    ovex
    cV
    cG
    cvtx
    cfv
    cvv
    iswlkg.v
    cG
    cvtx
    fvex
    eqeltri
    fpm
    elexd
    anim12i
    3adant3
    a1i
    @0
    @1
    @2
    @4
    @15
    wb
    cP
    cvv
    vk
    cF
    cG
    cI
    cV
    cW
    cvv
    iswlkg.v
    iswlkg.i
    iswlk
    3expib
    pm5.21ndd
end
