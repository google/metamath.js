include "crn.mm"
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
include "relelrn.mm"
include "syl2anc.mm"
include "wfn.mm"
include "ccnv.mm"
include "wfun.mm"
include "wceq.mm"
include "w3a.mm"
include "dff1o2.mm"
include "sylib.mm"
include "simp3d.mm"
include "eleqtrd.mm"

theorem ntrneinex
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
  assert |- ( ph -> N e. ( ~P ~P B ^m B ) )

  proof
    wph
    cN
    cF
    crn
    #
    cB
    cpw
    #
    cpw
    cB
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
    cN
    @0
    wcel
    wph
    @1
    @1
    cmap
    co
    #
    @2
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
    @4
    @2
    cF
    f1orel
    syl
    ntrnei.r
    cI
    cN
    cF
    relelrn
    syl2anc
    wph
    cF
    @4
    wfn
    #
    cF
    ccnv
    wfun
    #
    @0
    @2
    wceq
    #
    wph
    @5
    @7
    @8
    @9
    w3a
    @6
    @4
    @2
    cF
    dff1o2
    sylib
    simp3d
    eleqtrd
end
