include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "wf1o.mm"
include "ntrneif1o.mm"
include "f1ofn.mm"
include "syl.mm"
include "ntrneiiex.mm"
include "jca.mm"
include "fnfun.mm"
include "adantr.mm"
include "fndm.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "funbrfvb.mm"
include "3syl.mm"
include "mpbird.mm"

theorem ntrneifv1
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
  assert |- ( ph -> ( F ` I ) = N )

  proof
    wph
    cI
    cF
    cfv
    cN
    wceq
    #
    cI
    cN
    cF
    wbr
    #
    ntrnei.r
    wph
    cF
    cB
    cpw
    #
    @2
    cmap
    co
    #
    wfn
    #
    cI
    @3
    wcel
    #
    wa
    #
    cF
    wfun
    #
    cI
    cF
    cdm
    #
    wcel
    #
    wa
    @0
    @1
    wb
    wph
    @4
    @5
    wph
    @3
    @2
    cpw
    cB
    cmap
    co
    #
    cF
    wf1o
    @4
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
    @3
    @10
    cF
    f1ofn
    syl
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
    ntrneiiex
    jca
    @6
    @7
    @9
    @4
    @7
    @5
    @3
    cF
    fnfun
    adantr
    @4
    @9
    @5
    @4
    @8
    @3
    cI
    @3
    cF
    fndm
    eleq2d
    biimpar
    jca
    cI
    cN
    cF
    funbrfvb
    3syl
    mpbird
end
