include "cdm.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wrel.mm"
include "wbr.mm"
include "wcel.mm"
include "wf1o.mm"
include "ntrclsf1o.mm"
include "f1orel.mm"
include "syl.mm"
include "releldm.mm"
include "syl2anc.mm"
include "wceq.mm"
include "f1odm.mm"
include "eleqtrd.mm"

theorem ntrclsiex
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
  assert |- ( ph -> I e. ( ~P B ^m ~P B ) )

  proof
    wph
    cI
    cD
    cdm
    #
    cB
    cpw
    #
    @1
    cmap
    co
    #
    wph
    cD
    wrel
    #
    cI
    cK
    cD
    wbr
    cI
    @0
    wcel
    wph
    @2
    @2
    cD
    wf1o
    #
    @3
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
    #
    @2
    @2
    cD
    f1orel
    syl
    ntrcls.r
    cI
    cK
    cD
    releldm
    syl2anc
    wph
    @4
    @0
    @2
    wceq
    @5
    @2
    @2
    cD
    f1odm
    syl
    eleqtrd
end
