include "covoln.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "ovnval2.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqtrd.mm"

theorem ovnn0val
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cX: class X
  let vx: setvar x
  assume ovnn0val.1: |- ( ph -> X e. Fin )
  assume ovnn0val.2: |- ( ph -> X =/= (/) )
  assume ovnn0val.3: |- ( ph -> A C_ ( RR ^m X ) )
  assume ovnn0val.4: |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ( A C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) }

  disjoint A i
  disjoint A z
  disjoint i z
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X z
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint j z
  disjoint k z
  disjoint k x
  assert |- ( ph -> ( ( voln* ` X ) ` A ) = inf ( M , RR* , < ) )

  proof
    wph
    cA
    cX
    covoln
    cfv
    cfv
    cX
    c0
    wceq
    #
    cc0
    cM
    cxr
    clt
    cinf
    #
    cif
    @1
    wph
    vz
    cA
    vi
    vj
    vk
    cM
    cX
    ovnn0val.1
    ovnn0val.3
    ovnn0val.4
    ovnval2
    wph
    @0
    cc0
    @1
    wph
    cX
    c0
    ovnn0val.2
    neneqd
    iffalsed
    eqtrd
end
