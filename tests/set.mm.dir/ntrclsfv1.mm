include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wfn.mm"
include "wf1o.mm"
include "ntrclsf1o.mm"
include "f1ofn.mm"
include "syl.mm"
include "ntrclsiex.mm"
include "jca.mm"
include "fnfun.mm"
include "adantr.mm"
include "fndm.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "funbrfvb.mm"
include "mpbird.mm"

theorem ntrclsfv1
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
  assert |- ( ph -> ( D ` I ) = K )

  proof
    wph
    cI
    cD
    cfv
    cK
    wceq
    #
    cI
    cK
    cD
    wbr
    #
    ntrcls.r
    wph
    cD
    wfun
    #
    cI
    cD
    cdm
    #
    wcel
    #
    wa
    #
    @0
    @1
    wb
    wph
    cD
    cB
    cpw
    #
    @6
    cmap
    co
    #
    wfn
    #
    cI
    @7
    wcel
    #
    wa
    #
    @5
    wph
    @8
    @9
    wph
    @7
    @7
    cD
    wf1o
    @8
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
    @7
    @7
    cD
    f1ofn
    syl
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
    ntrclsiex
    jca
    @10
    @2
    @4
    @8
    @2
    @9
    @7
    cD
    fnfun
    adantr
    @8
    @4
    @9
    @8
    @3
    @7
    cI
    @7
    cD
    fndm
    eleq2d
    biimpar
    jca
    syl
    cI
    cK
    cD
    funbrfvb
    syl
    mpbird
end
