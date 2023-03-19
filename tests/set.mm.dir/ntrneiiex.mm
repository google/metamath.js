include "cdm.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wrel.mm"
include "wbr.mm"
include "wcel.mm"
include "wf1o.mm"
include "ntrneif1o.mm"
include "f1orel.mm"
include "syl.mm"
include "releldm.mm"
include "syl2anc.mm"
include "wceq.mm"
include "f1odm.mm"
include "eleqtrd.mm"

theorem ntrneiiex
  let wph: wff ph
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cI: class I
  let cN: class N
  let cO: class O
  let vl: setvar l
  assume ntrnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume ntrnei.f: |- F = ( ~P B O B )
  assume ntrnei.r: |- ( ph -> I F N )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint k l
  disjoint k m
  disjoint l m
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  assert |- ( ph -> I e. ( ~P B ^m ~P B ) )

  proof
    wph
    cI
    cF
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
    cF
    wrel
    #
    cI
    cN
    cF
    wbr
    cI
    @0
    wcel
    wph
    @2
    @1
    cpw
    cB
    cmap
    co
    #
    cF
    wf1o
    #
    @3
    wph
    cB
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    vl
    ntrnei.o
    ntrnei.f
    ntrnei.r
    ntrneif1o
    #
    @2
    @4
    cF
    f1orel
    syl
    ntrnei.r
    cI
    cN
    cF
    releldm
    syl2anc
    wph
    @5
    @0
    @2
    wceq
    @6
    @2
    @4
    cF
    f1odm
    syl
    eleqtrd
end
