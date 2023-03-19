include "ccnv.mm"
include "cvv.mm"
include "ntrclsbex.mm"
include "dssmapnvod.mm"
include "wbr.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf1o.mm"
include "wrel.mm"
include "wb.mm"
include "ntrclsf1o.mm"
include "f1orel.mm"
include "relbrcnvg.mm"
include "3syl.mm"
include "mpbird.mm"
include "breqdi.mm"

theorem ntrclsnvobr
  let wph: wff ph
  let cB: class B
  let cD: class D
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cI: class I
  let cK: class K
  let cO: class O
  assume ntrcls.o: |- O = ( i e. _V |-> ( k e. ( ~P i ^m ~P i ) |-> ( j e. ~P i |-> ( i \ ( k ` ( i \ j ) ) ) ) ) )
  assume ntrcls.d: |- D = ( O ` B )
  assume ntrcls.r: |- ( ph -> I D K )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint i ph
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> K D I )

  proof
    wph
    cD
    ccnv
    #
    cD
    cK
    cI
    wph
    cB
    cD
    vk
    cO
    cvv
    vj
    vi
    ntrcls.o
    ntrcls.d
    wph
    cB
    cD
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsbex
    dssmapnvod
    wph
    cK
    cI
    @0
    wbr
    #
    cI
    cK
    cD
    wbr
    #
    ntrcls.r
    wph
    cB
    cpw
    #
    @3
    cmap
    co
    #
    @4
    cD
    wf1o
    cD
    wrel
    @1
    @2
    wb
    wph
    cB
    cD
    vi
    vj
    vk
    cI
    cK
    cO
    ntrcls.o
    ntrcls.d
    ntrcls.r
    ntrclsf1o
    @4
    @4
    cD
    f1orel
    cK
    cI
    cD
    relbrcnvg
    3syl
    mpbird
    breqdi
end
