include "cfv.mm"
include "wceq.mm"
include "cdif.mm"
include "ntrclsfv.mm"
include "eqeq2d.mm"
include "ntrclsrcomplex.mm"
include "ntrclsfveq1.mm"
include "wss.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "ntrclskex.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "dfss4.mm"
include "sylib.mm"
include "3bitrd.mm"

theorem ntrclsfveq
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cS: class S
  let cT: class T
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cI: class I
  let cK: class K
  let cO: class O
  assume ntrcls.o: |- O = ( i e. _V |-> ( k e. ( ~P i ^m ~P i ) |-> ( j e. ~P i |-> ( i \ ( k ` ( i \ j ) ) ) ) ) )
  assume ntrcls.d: |- D = ( O ` B )
  assume ntrcls.r: |- ( ph -> I D K )
  assume ntrclsfv.s: |- ( ph -> S e. ~P B )
  assume ntrclsfv.t: |- ( ph -> T e. ~P B )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint K j
  disjoint K k
  disjoint S j
  disjoint T j
  disjoint i ph
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> ( ( I ` S ) = ( I ` T ) <-> ( K ` ( B \ S ) ) = ( K ` ( B \ T ) ) ) )

  proof
    wph
    cS
    cI
    cfv
    #
    cT
    cI
    cfv
    #
    wceq
    @0
    cB
    cB
    cT
    cdif
    #
    cK
    cfv
    #
    cdif
    #
    wceq
    cB
    cS
    cdif
    cK
    cfv
    #
    cB
    @4
    cdif
    #
    wceq
    @5
    @3
    wceq
    wph
    @1
    @4
    @0
    wph
    cB
    cD
    cT
    vi
    vj
    vk
    cI
    cK
    cO
    ntrcls.o
    ntrcls.d
    ntrcls.r
    ntrclsfv.t
    ntrclsfv
    eqeq2d
    wph
    cB
    @4
    cD
    cS
    vi
    vj
    vk
    cI
    cK
    cO
    ntrcls.o
    ntrcls.d
    ntrcls.r
    ntrclsfv.s
    wph
    cB
    cD
    @3
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsrcomplex
    ntrclsfveq1
    wph
    @6
    @3
    @5
    wph
    @3
    cB
    wss
    @6
    @3
    wceq
    wph
    @3
    cB
    wph
    cB
    cpw
    #
    @7
    @2
    cK
    wph
    cK
    @7
    @7
    cmap
    co
    wcel
    @7
    @7
    cK
    wf
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
    ntrclskex
    cK
    @7
    @7
    elmapi
    syl
    wph
    cB
    cD
    cT
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsrcomplex
    ffvelrnd
    elpwid
    @3
    cB
    dfss4
    sylib
    eqeq2d
    3bitrd
end
