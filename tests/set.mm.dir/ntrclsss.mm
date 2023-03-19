include "cfv.mm"
include "wss.mm"
include "cdif.mm"
include "ntrclsfv.mm"
include "sseq12d.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "ntrclskex.mm"
include "ancli.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "ntrclsrcomplex.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "jca.mm"
include "sscon34b.mm"
include "3syl.mm"
include "bitr4d.mm"

theorem ntrclsss
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
  assert |- ( ph -> ( ( I ` S ) C_ ( I ` T ) <-> ( K ` ( B \ T ) ) C_ ( K ` ( B \ S ) ) ) )

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
    wss
    cB
    cB
    cS
    cdif
    #
    cK
    cfv
    #
    cdif
    #
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
    wss
    #
    @6
    @3
    wss
    #
    wph
    @0
    @4
    @1
    @7
    wph
    cB
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
    ntrclsfv
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
    sseq12d
    wph
    wph
    cK
    cB
    cpw
    #
    @10
    cmap
    co
    wcel
    #
    wa
    #
    @6
    cB
    wss
    #
    @3
    cB
    wss
    #
    wa
    @9
    @8
    wb
    wph
    @11
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
    ancli
    @12
    @13
    @14
    @12
    @6
    cB
    @12
    @10
    @10
    @5
    cK
    @11
    @10
    @10
    cK
    wf
    wph
    cK
    @10
    @10
    elmapi
    adantl
    #
    wph
    @5
    @10
    wcel
    @11
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
    adantr
    ffvelrnd
    elpwid
    @12
    @3
    cB
    @12
    @10
    @10
    @2
    cK
    @15
    wph
    @2
    @10
    wcel
    @11
    wph
    cB
    cD
    cS
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsrcomplex
    adantr
    ffvelrnd
    elpwid
    jca
    @6
    @3
    cB
    sscon34b
    3syl
    bitr4d
end
