include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "cdm.mm"
include "wn.mm"
include "wlkcl.mm"
include "wlkp.mm"
include "jca.mm"
include "wceq.mm"
include "fzp1nel.mm"
include "a1i.mm"
include "oveq1i.mm"
include "eleq1i.mm"
include "sylnibr.mm"
include "eleq2.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "fdm.mm"
include "impel.mm"
include "3syl.mm"

theorem wlkp1lem1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  assume wlkp1.v: |- V = ( Vtx ` G )
  assume wlkp1.i: |- I = ( iEdg ` G )
  assume wlkp1.f: |- ( ph -> Fun I )
  assume wlkp1.a: |- ( ph -> I e. Fin )
  assume wlkp1.b: |- ( ph -> B e. _V )
  assume wlkp1.c: |- ( ph -> C e. V )
  assume wlkp1.d: |- ( ph -> -. B e. dom I )
  assume wlkp1.w: |- ( ph -> F ( Walks ` G ) P )
  assume wlkp1.n: |- N = ( # ` F )


  assert |- ( ph -> -. ( N + 1 ) e. dom P )

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
    chash
    cfv
    #
    cn0
    wcel
    #
    cc0
    @1
    cfz
    co
    #
    cV
    cP
    wf
    #
    wa
    cN
    c1
    caddc
    co
    #
    cP
    cdm
    #
    wcel
    #
    wn
    #
    wlkp1.w
    @0
    @2
    @4
    cP
    cF
    cG
    wlkcl
    cP
    cF
    cG
    cV
    wlkp1.v
    wlkp
    jca
    @2
    @6
    @3
    wceq
    #
    @8
    @4
    @2
    @8
    @9
    @5
    @3
    wcel
    #
    wn
    @2
    @1
    c1
    caddc
    co
    #
    @3
    wcel
    #
    @10
    @12
    wn
    @2
    cc0
    @1
    fzp1nel
    a1i
    @5
    @11
    @3
    cN
    @1
    c1
    caddc
    wlkp1.n
    oveq1i
    eleq1i
    sylnibr
    @9
    @7
    @10
    @6
    @3
    @5
    eleq2
    notbid
    syl5ibrcom
    @3
    cV
    cP
    fdm
    impel
    3syl
end
