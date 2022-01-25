################################################################################
## Base stage
################################################################################

ARG VARIANT=latest
FROM debian:${VARIANT} as base

RUN apt-get update \
  && apt-get -y install --no-install-recommends \
    ca-certificates \
    curl \
  && apt-get autoremove -y \
  && apt-get clean -y \
  && rm -rf /var/lib/apt/lists/*

################################################################################
## Elan build stage
################################################################################

FROM base as elan-build

ARG ELAN_RELEASE=v1.3.1

RUN curl https://raw.githubusercontent.com/leanprover/elan/${ELAN_RELEASE}/elan-init.sh -o /tmp/elan-init.sh \
  && chmod +x /tmp/elan-init.sh \
  && /tmp/elan-init.sh -y --default-toolchain none \
  && rm /tmp/elan-init.sh

################################################################################
## Final Stage
################################################################################

FROM base

RUN apt-get update \
  && apt-get -y install --no-install-recommends \
    sudo \
    bash \
    make \
    git \
    ssh \
  && apt-get autoremove -y \
  && apt-get clean -y \
  && rm -rf /var/lib/apt/lists/*

# Setup user

ARG USERNAME=vscode
ARG USER_UID=1000
ARG USER_GID=${USER_UID}

RUN groupadd --gid ${USER_GID} ${USERNAME} \
  && useradd --uid ${USER_UID} --gid ${USER_GID} -m ${USERNAME} -s /bin/bash \
  && echo "${USERNAME} ALL=\(root\) NOPASSWD:ALL" > /etc/sudoers.d/${USERNAME} \
  && chmod 0440 /etc/sudoers.d/${USERNAME}

# Setup elan

COPY --from=elan-build /root/.elan /home/${USERNAME}/.elan
RUN chown -R $USER_UID:$USER_GID /home/$USERNAME/.elan

# Setup lean

USER ${USERNAME}
WORKDIR /home/${USERNAME}

ENV PATH=/home/${USERNAME}/.elan/bin:${PATH}
RUN cat /home/${USERNAME}/.elan/env >> /home/${USERNAME}/.profile

COPY lean-toolchain /tmp/lean-toolchain
RUN elan default $(cat /tmp/lean-toolchain)
